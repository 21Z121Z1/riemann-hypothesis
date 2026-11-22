import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0231
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.LocalToGlobal.KernelLattices.Bundle0004
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0011
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Saturated
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0239
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormIntegrality
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.FactsLat

variable {D : D7}

theorem selfDual_frame_level_one_lattice_eq_standard {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : IsSDFrame V β Λ 1) :
    (Λ : Set (Fin V.rank → D.host.E)) = Formalism.MainNotions.StandardLattice.L0c D V := by
  obtain ⟨c, -, -, -, h1, h2⟩ := h
  simp only [one_pow, Nat.cast_one, one_smul] at h1 h2
  exact Set.ext fun x => ⟨h2 x, h1 x⟩

theorem pi_eq_stdL (E : Type) [Field E] [NumberField E] (n : ℕ) :
    (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) = stdL E n := by
  apply le_antisymm
  · intro x hx
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun a _ => ?_
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hx a trivial)
    have : (Pi.single a (x a) : Fin n → E) = b • (Pi.single a 1 : Fin n → E) := by
      rw [← Pi.single_smul, ← hb, Algebra.smul_def, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩ j -
    by_cases h : j = a
    · subst h
      exact Submodule.mem_one.2 ⟨1, by simp⟩
    · simp [h]

theorem arr_injective {n : ℕ} {q : ℕ} (hq : q ≤ n) : Function.Injective (arr q : Fin n → Fin n) := by
  intro a b h
  have h' := congrArg Fin.val h
  have := a.2
  have := b.2
  unfold arr at h'
  apply Fin.ext
  split_ifs at h' <;> simp only at h' <;> omega

section Model

variable {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {p q : ℕ} (hpq : p + q = V.rank)
  (hε : ∀ τ a, M.ε τ a = decide ((a : ℕ) < p))
include hpq hε

theorem nNeg_eq (τ : D.what₂.Tau) : nNeg (M.ε τ) = q := by
  rw [nNeg_shape (by omega) (hε τ)]; omega

theorem negM_eq (τ : D.what₂.Tau) :
    negM V q = diagonal fun c => (if M.ε τ (arr (nNeg (M.ε τ)) c) = true then (1 : ℂ) else -1) := by
  unfold negM
  congr 1
  funext c
  have := c.2
  rw [nNeg_eq M hpq hε, hε, arr, sgn]
  by_cases h : (c : ℕ) < q
  · rw [dif_pos h, if_pos h, if_neg (by simp only [decide_eq_true_eq]; omega)]; simp
  · rw [dif_neg h, if_neg h, if_pos (by simp only [decide_eq_true_eq]; omega)]; simp

theorem isONeg_x0Mat : IsONeg V q (x0Mat M) := by
  intro τ
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have h2 : (onb M τ)ᴴ * gramAt D V τ * onb M τ = Formalism.REAL.Jm (M.ε τ) := by
    rw [← M.fr_gram τ]; unfold onb
    calc _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp
  have h3 : (x0Mat M τ)ᴴ * gramAt D V τ * x0Mat M τ =
      ((onb M τ)ᴴ * gramAt D V τ * onb M τ).submatrix (arr (nNeg (M.ε τ))) (arr (nNeg (M.ε τ))) := rfl
  rw [h3, h2, negM_eq M hpq hε τ, Formalism.REAL.Jm, Matrix.submatrix_diagonal _ _ (arr_injective (nNeg_le _))]
  rfl

theorem cart_eq_cartZ : cart M = cartZ V q (x0Mat M) := by
  funext τ
  have hn : negM V q * negM V q = 1 := by
    rw [negM_eq M hpq hε τ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext a; split_ifs <;> simp
  have h1 : (negM V q * ((x0Mat M τ)ᴴ * gramAt D V τ)) * x0Mat M τ = 1 := by
    rw [Matrix.mul_assoc, isONeg_x0Mat M hpq hε τ, hn]
  have hu : IsUnit (x0Mat M τ).det := Matrix.isUnit_det_of_left_inverse h1
  rw [cartZ, negM_eq M hpq hε τ, ← torus_x0Mat M τ fun a => if M.ε τ a = true then (1 : ℂ) else -1,
    Matrix.mul_nonsing_inv_cancel_right _ _ hu]
  rfl

end Model

theorem muVal_cast {V W : HSp D} (hV : V = W) {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : MuVal V χ mu) :
    MuVal W χ (castDict hV mu) := by
  subst hV; exact h

theorem latEmb_cast {V W : HSp D} (hV : V = W) {r : ℕ} (hr : V.rank = r) (hr' : W.rank = r) {La : Type} [AddCommGroup La]
    [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin r → D.host.E))
    (h : LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι)) :
    LatEmb W (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr') ∘ₗ ι) := by
  subst hV; exact h

theorem isAA_span {k : ℕ} (L : Lt D.host.E k) : GlobalTheory.Ker.IsAA (Submodule.span (𝓞 D.host.E)
    {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ L, w = a • v}) L := by
  intro v
  rw [← Submodule.mem_toAddSubgroup]
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx => exact AddSubgroup.subset_closure hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x hx' hx =>
      clear hx'
      induction hx using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨a, ha, t, ht, rfl⟩ := hx
        exact AddSubgroup.subset_closure ⟨a, ha, c • t, L.smul_mem c ht, smul_comm _ _ _⟩
      | zero => rw [smul_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
      | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  · intro hv
    exact (AddSubgroup.closure_le _).2 (fun x hx => Submodule.subset_span hx) hv

theorem isMov_hLat (W : HSp D) (h : GA D W) :
    GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt W h) (Bridge.hLat W 1) (Bridge.hLat W (FWT.fin W h)) := by
  intro u
  rw [GlobalTheory.MovedLat.hLat_one]
  have := Set.ext_iff.1 (GlobalTheory.MovedLat.hat_hLat W (FWT.fin W h)) u
  exact this.trans ⟨fun ⟨z, hz, e⟩ => ⟨z, hz, e.symm⟩, fun ⟨z, hz, e⟩ => ⟨z, hz, e.symm⟩⟩

end GlobalTheory.OneMapRef.FactsLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdOfMemSupport
section
noncomputable section

namespace GlobalTheory.KerRescale

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G Formalism.L2.Ker Classical

theorem card_eq_sum_colLen (μ : YoungDiagram) : μ.card = ∑ c : Fin (μ.rowLen 0), μ.colLen c := by
  have hmap : ∀ c ∈ μ.cells, c.2 ∈ Finset.range (μ.rowLen 0) := by
    intro c hc
    rw [Finset.mem_range]
    have h1 : (c.1, c.2) ∈ μ := hc
    have h2 : (0, c.2) ∈ μ := μ.up_left_mem (Nat.zero_le _) le_rfl h1
    exact YoungDiagram.mem_iff_lt_rowLen.1 h2
  unfold YoungDiagram.card
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (fun c hc => hmap c hc),
    Fin.sum_univ_eq_sum_range (fun c => μ.colLen c)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [YoungDiagram.colLen_eq_card]
  rfl

section Hom

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ) {K : Type} [CommMonoid K] (a : Lt → K)

def wt : KM.XZ Lt N0 N1 → Additive K := Sum.elim (fun _ => 0) (fun z => Additive.ofMul (a z.1))

theorem minorXZ_hom (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) :
    MvPolynomial.IsWeightedHomogeneous (wt N0 N1 a) (KM.minorXZ N0 N1 s p I) (p • Additive.ofMul (a s)) := by
  have hent : ∀ i k : Fin p, MvPolynomial.IsWeightedHomogeneous (wt N0 N1 a)
      (∑ b : Fin N0, MvPolynomial.X (Sum.inl (s, (i : ℕ), b)) * MvPolynomial.X (Sum.inr (s, b, I k)) :
        MvPolynomial (KM.XZ Lt N0 N1) ℤ) (Additive.ofMul (a s)) := by
    intro i k
    refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_
    have := (MvPolynomial.isWeightedHomogeneous_X ℤ (wt N0 N1 a) (Sum.inl (s, (i : ℕ), b))).mul
      (MvPolynomial.isWeightedHomogeneous_X ℤ (wt N0 N1 a) (Sum.inr (s, b, I k)))
    simpa only [wt, Sum.elim_inl, Sum.elim_inr, zero_add] using this
  unfold KM.minorXZ
  rw [Matrix.det_apply]
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  rw [Units.smul_def]
  apply Submodule.smul_mem (MvPolynomial.weightedHomogeneousSubmodule ℤ (wt N0 N1 a) _)
  have := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ (fun _ => Additive.ofMul (a s))
    (fun i _ => hent (σ i) i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at this
  exact this

theorem Gxz_hom (nu : Lt → YoungDiagram) (I : KM.ColChoice N1 nu) :
    MvPolynomial.IsWeightedHomogeneous (wt N0 N1 a) (KM.Gxz N0 N1 nu I) (∑ s, (nu s).card • Additive.ofMul (a s)) := by
  unfold KM.Gxz
  refine MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ _ fun s _ => ?_
  rw [card_eq_sum_colLen, Finset.sum_smul]
  exact MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ _ fun c _ => minorXZ_hom N0 N1 a s _ (I s c)

theorem prod_of_mem_support (nu : Lt → YoungDiagram) (I : KM.ColChoice N1 nu) (μ : KM.XZ Lt N0 N1 →₀ ℕ)
    (hμ : μ ∈ (KM.Gxz N0 N1 nu I).support) :
    ((Finsupp.sumFinsuppEquivProdFinsupp μ).2.prod fun z n => a z.1 ^ n) = ∏ s, a s ^ (nu s).card := by
  have h := Gxz_hom N0 N1 a nu I (MvPolynomial.mem_support_iff.mp hμ)
  have hμ' : μ = Finsupp.sumElim (Finsupp.sumFinsuppEquivProdFinsupp μ).1 (Finsupp.sumFinsuppEquivProdFinsupp μ).2 := by
    ext x; cases x <;> simp
  rw [hμ', Finsupp.weight_apply, Finsupp.sum_sumElim] at h
  generalize Finsupp.sumFinsuppEquivProdFinsupp μ = p at h ⊢
  have h2 := congrArg Additive.toMul h
  unfold Finsupp.sum at h2
  simp only [Function.comp_apply, wt, Sum.elim_inl, Sum.elim_inr, smul_zero, Finset.sum_const_zero, zero_add, toMul_sum,
    toMul_nsmul, toMul_ofMul] at h2
  exact h2

end Hom

theorem applyAt0_rescale {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ) (l : ℕ) [Fact l.Prime] (a : Lt → ℂ_[l])
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (nu : Lt → YoungDiagram) (I : KM.ColChoice N1 nu) :
    KM.applyAt0 N0 N1 l (MvPowerSeries.rescale (fun z => a z.1) Th) (KM.Gxz N0 N1 nu I) =
      (∏ s, a s ^ (nu s).card) • KM.applyAt0 N0 N1 l Th (KM.Gxz N0 N1 nu I) := by
  unfold KM.applyAt0
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [MvPowerSeries.coeff_rescale, prod_of_mem_support N0 N1 a nu I μ hμ, MvPolynomial.smul_monomial, smul_eq_mul]
  congr 1
  ring

theorem rescale_atLin {σ κ : Type} [Finite σ] [Fintype κ] {p : ℕ} [Fact p.Prime] (c : σ → κ → ℂ_[p]) (a : κ → ℂ_[p])
    (F : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries.rescale a (atLin c (fun j => MvPowerSeries.X j) F) =
      atLin (fun k j => a j * c k j) (fun j => MvPowerSeries.X j) F := by
  unfold atLin
  have hs : MvPowerSeries.HasSubst (fun k : σ => ∑ j : κ, algebraMap ℂ_[p] (MvPowerSeries κ ℂ_[p]) (c k j) * MvPowerSeries.X j) := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => ?_
    simp [map_sum]
  rw [MvPowerSeries.rescale_eq_subst, MvPowerSeries.subst_comp_subst_apply hs (MvPowerSeries.HasSubst.smul_X a)]
  congr 1
  funext k
  rw [← MvPowerSeries.rescale_eq_subst, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Algebra.smul_def, ← Algebra.smul_def, ← MvPowerSeries.rescaleAlgHom_apply, map_smul, MvPowerSeries.rescaleAlgHom_apply,
    MvPowerSeries.rescale_eq_subst, MvPowerSeries.subst_X (MvPowerSeries.HasSubst.smul_X a)]
  show c k j • (a j • (MvPowerSeries.X j : MvPowerSeries κ ℂ_[p])) = (a j * c k j) • (MvPowerSeries.X j : MvPowerSeries κ ℂ_[p])
  rw [mul_comm, mul_smul]

variable {D : D7} (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (B : PlaceMatrixFamily D) {Dx : DivX D} {Tw : TwForms D}
  (a : ∀ w : D.what₂.places.Pl, D.what₂.Word → D.what₂.Tup → D.what₂.Tau → Cw D w)

def kerEntR (ha : ∀ w u μ τ, ‖a w u μ τ‖ = 1) (h : KerEntHyp P O B Dx Tw) : KerEnt D Dx Tw where
  lam := P.lam
  iL := P.iL
  iL_lam := P.iL_lam
  iL_int := P.iL_int
  Th := fun u μ w i c c' => MvPowerSeries.rescale (fun z => a w u μ (tauPl D z.1)) (thAtW P O B u μ w i c c')
  VQ := fun u μ i _ => ValQ O u μ i
  ev := fun u μ i _ => evC O u μ i
  ev_inj := fun u μ i _ => evC_inj O u μ i
  prS := prSC P O B
  prT := prTC P O B
  prT_val := h.val
  lat_S := h.latS
  levelFree_lattice_condition := h.latT
  un := fun u μ w i c c' => (∏ z : Bool × HH D, a w u μ (tauPl D z) ^ (nuD D u i z).card)⁻¹ * unC P O B u μ w i c c'
  un_ne := fun u μ w i c c' => mul_ne_zero
    (inv_ne_zero (Finset.prod_ne_zero_iff.2 fun z _ => pow_ne_zero _ (norm_ne_zero_iff.1 (by rw [ha]; exact one_ne_zero))))
    (unC_ne P O B u μ w i c c')
  kform := fun u μ w hw i hi c c' v v' hv I => by
    have h0 : (∏ z : Bool × HH D, a w u μ (tauPl D z) ^ (nuD D u i z).card) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun z _ => pow_ne_zero _ (norm_ne_zero_iff.1 (by rw [ha]; exact one_ne_zero))
    rw [h.kform u μ w hw i hi c c' v v' hv I, applyAt0_rescale _ _ _ (fun z => a w u μ (tauPl D z)), map_smul, smul_eq_mul]
    field_simp

theorem kerEntR_Th (ha : ∀ w u μ τ, ‖a w u μ τ‖ = 1) (h : KerEntHyp P O B Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (i : ℕ) (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) :
    (kerEntR P O B a ha h).Th u μ w i c c' =
      atLin (fun (k : D.what₂.Tau × Fin (D.R.N (i + 1)) × Fin (D.R.N i)) (j : (Bool × HH D) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) =>
        if tauPl D j.1 = k.1 then
          a w u μ k.1 * lamC (P.lam w) ((O u μ).dgen k.1) * B u μ w (i + 1) c' k.1 k.2.1 j.2.2 * (B u μ w i c k.1)⁻¹ j.2.1 k.2.2
        else 0)
      (fun j => MvPowerSeries.X j) (pSer D (P.lam w) ((O u μ).Th i c c')) := by
  show MvPowerSeries.rescale _ (thAtW P O B u μ w i c c') = _
  unfold thAtW
  rw [rescale_atLin]
  congr 1
  funext k j
  split_ifs with hk
  · rw [hk]; ring
  · exact mul_zero _

def tieR (ha : ∀ w u μ τ, ‖a w u μ τ‖ = 1) (hB : BasOk P O B) (hC : CanOnto P) (h : KerEntHyp P O B Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) : GL3Columns.KFTie (kerEntR P O B a ha h) (O u μ) w where
  B := fun i c τ => B u μ w i c τ
  B_bas := fun i hi c τ => hB u μ w i hi c τ
  c0 := fun _ _ _ τ => a w u μ τ
  unitAbs_eq_one := fun _ _ _ τ => ha w u μ τ
  th := fun i _ c c' => kerEntR_Th P O B a ha h u μ w i c c'
  prS_can := (kfTieOf P O B hB hC h u μ w).prS_can
  prT_can := (kfTieOf P O B hB hC h u μ w).prT_can

theorem tieR_un (ha : ∀ w u μ τ, ‖a w u μ τ‖ = 1) (hB : BasOk P O B) (hC : CanOnto P) (h : KerEntHyp P O B Dx Tw) (u : D.what₂.Word)
    (μ : D.what₂.Tup) (hR : GL3Columns.RhoAlg (O u μ)) (w : D.what₂.places.Pl) : (tieR P O B a ha hB hC h u μ w).UnIs := by
  intro i hi c c'
  show _ * unC P O B u μ w i c c' = _
  unfold unC
  rw [if_neg (unF_ne P O B hB u μ hR w i hi c c')]
  unfold GL3Columns.KFTie.un
  rw [mul_assoc]
  rfl

theorem tauEmb_mem (w : D.what₂.places.Pl) (τ : D.what₂.Tau) (x : D.host.E) : ∃ y : D.what₂.LL, tauEmb D (P.lam w) τ x = P.iL w y := by
  have e : D.what₂.embLL (D.embE (D.host.sigmaOf (D.eTau τ : D.R.GG) x)) = embT D τ x := RingHom.congr_fun D.embE_φ₀ _
  refine ⟨D.embE (D.host.sigmaOf (D.eTau τ : D.R.GG) x), ?_⟩
  rw [P.iL_lam, e]
  rfl

def adUnit (w : D.what₂.places.Pl) (u : D.what₂.Word) (μ : D.what₂.Tup) (τ : D.what₂.Tau) : Cw D w :=
  if AdPl D w then (lamC (P.lam w) ((O u μ).dgen τ))⁻¹ else 1

theorem norm_adUnit (hU : DgenUnitAd P O) (w : D.what₂.places.Pl) (u : D.what₂.Word) (μ : D.what₂.Tup) (τ : D.what₂.Tau) :
    ‖adUnit P O w u μ τ‖ = 1 := by
  unfold adUnit
  split_ifs with hw
  · rw [norm_inv, hU w hw u μ τ, inv_one]
  · exact norm_one

theorem adaptedTh_kerEntR (hU : DgenUnitAd P O) (Pm : ∀ (_ : D.what₂.places.Pl) u μ, SysFam D u μ)
    (h1 : ∀ w u μ i, i ≤ D.R.m → ∀ c τ, GL3Columns.BasR D (P.lam w) τ ((O u μ).lat i c).1 ((Pm w u μ i c τ).map (tauEmb D (P.lam w) τ)))
    (h2 : ∀ w u μ i, i ≤ D.R.m → ∀ c τ τ', SamePr (P.lam w) τ τ' → Pm w u μ i c τ' = Pm w u μ i c τ)
    (h3 : ∀ w u μ i, i ≤ D.R.m → ∀ c τ τ', ConjPr (P.lam w) τ τ' → Pm w u μ i c τ' = dualM (Pm w u μ i c τ))
    (h : KerEntHyp P O (fun u μ w i c τ => (Pm w u μ i c τ).map (tauEmb D (P.lam w) τ)) Dx Tw) :
    AdaptedTh (kerEntR P O _ (adUnit P O) (norm_adUnit P O hU) h) O := by
  intro w hw u μ _
  refine ⟨Pm w u μ, h1 w u μ, h2 w u μ, h3 w u μ, fun i _ c c' => ?_⟩
  rw [kerEntR_Th]
  congr 1
  funext k j
  unfold adCoef adUnit
  have hs : lamC (P.lam w) ((O u μ).dgen k.1) ≠ 0 := norm_ne_zero_iff.1 (by rw [hU w hw u μ k.1]; exact one_ne_zero)
  rw [if_pos hw, inv_mul_cancel₀ hs, one_mul]
  rfl

end GlobalTheory.KerRescale

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpectralRedivisionTermEquivKeepsTermData
section
open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.SRe

variable (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (t : RT Y u u')

set_option maxHeartbeats 4000000 in
theorem re_termIsId : Formalism.L2.SG.FourParts.termIsId t ↔ Formalism.L2.SG.FourParts.termIsId (eRT Z Y u u' t) := (by with_unfolding_all exact (Iff.rfl (a := Formalism.L2.SG.FourParts.termIsId t) :))

set_option maxHeartbeats 4000000 in
theorem re_termInS : Formalism.L2.SG.FourParts.termInS t ↔ Formalism.L2.SG.FourParts.termInS (eRT Z Y u u' t) := (by with_unfolding_all exact (Iff.rfl (a := Formalism.L2.SG.FourParts.termInS t) :))

set_option maxHeartbeats 4000000 in
theorem re_relevant : t.relevant ↔ (eRT Z Y u u' t).relevant := (by with_unfolding_all exact (Iff.rfl (a := t.relevant) :))

set_option maxHeartbeats 4000000 in
theorem re_FeqF : t.FeqF ↔ (eRT Z Y u u' t).FeqF := (by with_unfolding_all exact (Iff.rfl (a := t.FeqF) :))

set_option maxHeartbeats 4000000 in
theorem re_generic : t.generic ↔ (eRT Z Y u u' t).generic := (by with_unfolding_all exact (Iff.rfl (a := t.generic) :))

set_option maxHeartbeats 4000000 in
theorem re_G : t.G = (eRT Z Y u u' t).G := (by with_unfolding_all exact (Eq.refl t.G :))

set_option maxHeartbeats 4000000 in
theorem re_termBBne : ∀ p, Formalism.L2.SG.Saturated.termBBne t p ↔ Formalism.L2.SG.Saturated.termBBne (eRT Z Y u u' t) p := (by with_unfolding_all exact (fun p => Iff.rfl (a := Formalism.L2.SG.Saturated.termBBne t p) :))

set_option maxHeartbeats 4000000 in
theorem re_ptOf : Formalism.L2.SG.PairVal.ptOf t = Formalism.L2.SG.PairVal.ptOf (eRT Z Y u u' t) := (by with_unfolding_all exact (Eq.refl (Formalism.L2.SG.PairVal.ptOf t) :))

set_option maxHeartbeats 4000000 in
theorem re_massTerm : Formalism.L2.SG.PairVal.massTerm t = Formalism.L2.SG.PairVal.massTerm (eRT Z Y u u' t) := (by with_unfolding_all exact (Eq.refl (Formalism.L2.SG.PairVal.massTerm t) :))

set_option maxHeartbeats 4000000 in
theorem re_cTerm : Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) t = Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) (reY Z Y).δ (reY Z Y).M) (eRT Z Y u u' t) := by
  kexactB Eq.refl (Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) t)

omit t in
set_option maxHeartbeats 4000000 in
theorem re_meanCount : ∀ w, Formalism.L2.SG.PairVal.meanCount D u u' (X.Fu u) (Y.what₂ u) w = Formalism.L2.SG.PairVal.meanCount (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) w := (by with_unfolding_all exact (fun w => Eq.refl (Formalism.L2.SG.PairVal.meanCount D u u' (X.Fu u) (Y.what₂ u) w) :))

omit t in
set_option maxHeartbeats 4000000 in

theorem eRT_keeps_term_data : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), (∀ t : RT Y u u', (Formalism.L2.SG.FourParts.termIsId t ↔ Formalism.L2.SG.FourParts.termIsId (eRT Z Y u u' t)) ∧ (Formalism.L2.SG.FourParts.termInS t ↔ Formalism.L2.SG.FourParts.termInS (eRT Z Y u u' t)) ∧ (t.relevant ↔ (eRT Z Y u u' t).relevant) ∧ (t.FeqF ↔ (eRT Z Y u u' t).FeqF) ∧ (t.generic ↔ (eRT Z Y u u' t).generic) ∧ t.G = (eRT Z Y u u' t).G ∧ (∀ p, Formalism.L2.SG.Saturated.termBBne t p ↔ Formalism.L2.SG.Saturated.termBBne (eRT Z Y u u' t) p) ∧ Formalism.L2.SG.PairVal.ptOf t = Formalism.L2.SG.PairVal.ptOf (eRT Z Y u u' t) ∧ Formalism.L2.SG.PairVal.massTerm t = Formalism.L2.SG.PairVal.massTerm (eRT Z Y u u' t) ∧ Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) t = Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) (reY Z Y).δ (reY Z Y).M) (eRT Z Y u u' t)) ∧ ∀ w, Formalism.L2.SG.PairVal.meanCount D u u' (X.Fu u) (Y.what₂ u) w = Formalism.L2.SG.PairVal.meanCount (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) w :=
  fun D Z X Y u u' => ⟨fun t => ⟨re_termIsId D Z X Y u u' t, re_termInS D Z X Y u u' t,
    re_relevant D Z X Y u u' t, re_FeqF D Z X Y u u' t, re_generic D Z X Y u u' t, re_G D Z X Y u u' t,
    re_termBBne D Z X Y u u' t, re_ptOf D Z X Y u u' t, re_massTerm D Z X Y u u' t,
    re_cTerm D Z X Y u u' t⟩, re_meanCount D Z X Y u u'⟩

end GlobalTheory.Mem.SRe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubsetImageOfIsClosedImmersion
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem support_pushforward_subset_image_of_isClosedImmersion :
    ∀ {X Y : Scheme.{0}} (g : Y ⟶ X) [IsClosedImmersion g] (E : Y.Modules),
      support ((Scheme.Modules.pushforward g).obj E) ⊆ g '' support E := by
  intro X Y g _ E y hy
  by_contra hyn
  rw [mem_support_iff, ← not_subsingleton_iff_nontrivial] at hy
  apply hy
  have hemb := g.isClosedEmbedding
  refine subsingleton_of_forall_eq 0 fun t => ?_
  obtain ⟨U, hyU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ t

  let Z0 : Set Y := {z | ∃ hz : z ∈ g ⁻¹ᵁ U, E.presheaf.germ (g ⁻¹ᵁ U) z hz s = 0}
  have hZ0 : IsOpen Z0 := by
    rw [isOpen_iff_forall_mem_open]
    rintro z ⟨hz, hzs⟩
    obtain ⟨W, hzW, iU, iV, he⟩ := TopCat.Presheaf.germ_eq E.presheaf z hz hz s 0
      (by rw [hzs, map_zero])
    refine ⟨W, fun z' hz' => ⟨(leOfHom iU) hz', ?_⟩, W.2, hzW⟩
    have := TopCat.Presheaf.germ_res_apply E.presheaf iU z' hz' s
    rw [he, map_zero, map_zero] at this
    exact this.symm
  obtain ⟨V', hV', hV'e⟩ := hemb.isInducing.isOpen_iff.1 hZ0
  let V : X.Opens := U ⊓ ⟨V' ∪ (Set.range g)ᶜ, hV'.union hemb.isClosed_range.isOpen_compl⟩
  have hyV : y ∈ V := by
    refine ⟨hyU, ?_⟩
    by_cases hr : y ∈ Set.range g
    · obtain ⟨z, rfl⟩ := hr
      have hzs : z ∉ support E := fun h => hyn ⟨z, h, rfl⟩
      have hz : z ∈ g ⁻¹ᵁ U := hyU
      refine Or.inl (show z ∈ g ⁻¹' V' from hV'e ▸ ⟨hz, (notMem_support_iff.1 hzs).elim _ _⟩)
    · exact Or.inr hr
  have hVU : V ≤ U := inf_le_left
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hVU) y hyV]
  have h0 : ((Scheme.Modules.pushforward g).obj E).presheaf.map (homOfLE hVU).op s = 0 := by
    refine section_eq_zero_of_germ (F := E) _ fun z hz => ?_
    have hz' : z ∈ Z0 := by
      rw [← hV'e]
      rcases hz.2 with h | h
      · exact h
      · exact absurd ⟨z, rfl⟩ h
    obtain ⟨hzU, hzs⟩ := hz'
    rw [Scheme.Modules.pushforward_obj_presheaf_map]
    exact (TopCat.Presheaf.germ_res_apply E.presheaf ((Opens.map g.base).map (homOfLE hVU)) z hz s).trans hzs
  rw [h0, map_zero]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VolumesAgreeAdelicOfTrueVolume
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem volTieG_of_trueVol : ∀ D : D7, letI := D.host.cmStar;
    (∀ W, D.vol W = trueVol D.sp.cm (Formalism.BasicNotions.TH.tauE D) D.cd W) → Formalism.L2.Theta.VolTieG D := by
  intro D
  letI := D.host.cmStar
  intro h
  rw [volTieG_iff]
  intro W hW
  rw [h W]
  exact GlobalTheory.T.unitaryAdelicQuotientVolume_is_volume _ _ D.sp.cm _ _ D.cd W (isCMFam_host _ D.host _ D.eTau) hW

end GlobalTheory.Mem.Vol
end

