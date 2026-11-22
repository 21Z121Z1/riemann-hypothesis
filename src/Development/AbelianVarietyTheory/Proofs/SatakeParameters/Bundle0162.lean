import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAct
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0140
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0028
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0151
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalSeriesAppendEquivParabolicProduct
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0123
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0041
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0152
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointLocalEigenGaloisPolynomialSplit
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

noncomputable section

namespace GlobalTheory.PtLocalEig
open Formalism.L2

theorem not_bad_of_genAt {D : D7} {M : Formalism.L2.MtFam D} (T : Formalism.L2.NormalizedLocalCompatibility D M) (j : ℕ) (w : D.what₂.places.Pl)
    (i : D.nd.Loc) (h : i ∈ D.nd.locs j w) (v : PlE D.host) (k : ℕ) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (hvk : Formalism.L2.GenAt D (D.what₂.places.resChar w) (T.B.Qc j w) v k) (hc : IsConjPl D.host v s.w) :
    s.v ∉ Formalism.L2.badPl D i := by
  intro hmem
  obtain ⟨w', hover, hw'⟩ := hmem
  obtain ⟨-, e2⟩ := (D.nd.locs_mem j w i).1 h
  have hl : D.nd.l i = D.what₂.places.resChar w := by rw [← D.nd.w_l i, e2]
  have hp : ∀ p : ℕ, w' ∈ placesOver D.host.E p → v ∈ placesOver D.host.E p := by
    intro p hp
    have h1 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
        w'.asIdeal := by rw [map_natCast]; exact hp
    have h2 : (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal := by
      rw [← hover]; exact h1
    have h3 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
        s.w.asIdeal := by
      rw [← Ideal.mem_comap, s.w_under]; exact h2
    rw [map_natCast] at h3
    exact (hc (p : 𝓞 D.host.E) (p : 𝓞 D.host.E) (by simp)).2 h3
  rcases hw' with hQ | ⟨kk, hg⟩ | hpd
  · rw [T.Q_eq j w i h] at hQ
    have hsw : s.w ∈ T.B.Qc j w := T.B.Qc_over j w w' s.w hQ ⟨s.v, hover, s.w_under⟩
    exact hvk.2.2.2.1 (T.B.Qc_conj j w v s.w hsw hc)
  · apply hvk.2.2.1
    refine ⟨?_, hvk.2.1⟩
    have hv := hp _ hg
    fin_cases kk
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
  · apply hvk.2.2.1
    refine ⟨?_, hvk.2.1⟩
    rw [hl] at hpd
    exact Or.inr (Or.inr (hp _ hpd))

theorem main : ∀ (D : D7) (M : Formalism.L2.MtFam D), Formalism.L2.HeckeTied D M → Formalism.L2.HeckeRational D M → Formalism.L2.AVTied D M → Formalism.L2.NormalizedLocalCompatibility D M → ∀ i : D.nd.Loc, (∀ (P : D.naut.AV i) (w : PlE D.host), SplitOut D.nd i w → ∃ lam : ℕ → ℂ, galPol D.naut (D.naut.lpTw (D.naut.locV i P w) ((1 - (D.R.nV : ℝ)) / 2)) = X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV, C ((-1) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * lam k) * X ^ (D.R.nV - k) ∧ ∀ (k : ℕ) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host w s.w → Formalism.AUTREP.IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ D.naut.typeV i P, Formalism.L2.NG.tN (M.loc i).J s ϖ k ((M.loc i).real y) = lam k • (M.loc i).real y) → GlobalTheory.ThetaExh.PtLocal D.nd D.naut i := by
  intro D M HT HR AV NL i hyp P x hcong
  classical
  have tN0 : ∀ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ),
      Formalism.L2.NG.tN (M.loc i).J s ϖ k (0 : Formalism.AUTREP.GAf D.host.E D.R.nV → (M.loc i).wt.W) = 0 := by
    intro s ϖ k; ext g; simp [Formalism.L2.NG.tN, Formalism.L2.NG.heckeD]
  by_cases hP0 : D.naut.typeV i P = ⊥
  · refine ⟨x, (AV.ptV i P x).2 ?_⟩
    intro v k s ϖ _ _ _ _ _ y hy
    rw [hP0, Submodule.mem_bot] at hy
    subst hy
    rw [map_zero, smul_zero, tN0]
  obtain ⟨y0, hy0, hy0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  have h : i ∈ D.nd.locs (D.nd.j i) (D.nd.w i) := (D.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  let lamF : PlE D.host → ℕ → ℂ := fun v =>
    if hv : SplitOut D.nd i v then Classical.choose (hyp P v hv) else 0
  have hlamF : ∀ v (hv : SplitOut D.nd i v), lamF v = Classical.choose (hyp P v hv) := fun v hv => dif_pos hv
  have hinjO : Function.Injective (iotaO D.nd D.naut i) := by
    unfold iotaO
    simp only [RingHom.coe_comp]
    exact (D.naut.iotaQC i).injective.comp ((D.naut.iotaQ i).injective.comp
      (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))))
  have hcoef : ∀ v k, SplitOut D.nd i v → 1 ≤ k → k ≤ D.R.nV → ∃ a : D.nd.O i,
      iotaO D.nd D.naut i a = lamF v k ∧
      IsLocalRing.residue (D.nd.O i) a = IsLocalRing.residue (D.nd.O i) ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x) := by
    intro v k hv hk1 hk2
    obtain ⟨p, hp1, hp2⟩ := hcong v hv
    have e1 := (Classical.choose_spec (hyp P v hv)).1
    rw [← hlamF v hv] at e1
    exact coeff_extract (iotaO D.nd D.naut i) hinjO D.R.nV (normV v) (normV_unit D i v hv.2.1) p (lamF v)
      (fun k => (D.nd.hT i v k : D.nd.X i → D.nd.O i) x) (hp1.trans e1) hp2 k hk1 hk2
  let aF : PlE D.host → ℕ → D.nd.O i := fun v k =>
    if hv : SplitOut D.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV then Classical.choose (hcoef v k hv.1 hv.2.1 hv.2.2) else 0
  have haF : ∀ v k (hv : SplitOut D.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV), iotaO D.nd D.naut i (aF v k) = lamF v k ∧
      IsLocalRing.residue (D.nd.O i) (aF v k) =
        IsLocalRing.residue (D.nd.O i) ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x) := by
    intro v k hv
    simp only [aF, dif_pos hv]
    exact Classical.choose_spec (hcoef v k hv.1 hv.2.1 hv.2.2)
  have hiotaC : ∀ z, iotaO D.nd D.naut i z = NL.iotaC _ _ (NL.phO _ _ i h z) := NL.iotaC_coh _ _ i h
  have hinjC : Function.Injective (NL.iotaC (D.nd.j i) (D.nd.w i)) := by
    intro a b hab
    have e2 : (NL.phO _ _ i h).symm a = (NL.phO _ _ i h).symm b := hinjO (by
      rw [hiotaC, hiotaC, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]; exact hab)
    simpa using congrArg (NL.phO _ _ i h) e2
  let φ : FractionRing (NL.B.Oc (D.nd.j i) (D.nd.w i)) →+* ℂ := IsFractionRing.lift hinjC
  have hφalg : ∀ z, φ (algebraMap _ _ z) = NL.iotaC _ _ z := fun z => IsFractionRing.lift_algebraMap hinjC z
  have hφK : φ.comp (NL.phK _ _ i h).toRingHom = (D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (D.nd.O i))
    ext z
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, NL.phK_alg, hφalg]
    rw [← hiotaC]
    rfl
  have hφ : ∀ y, φ (NL.B.ec _ _ y) = D.what₂.embLL y := by
    intro y
    rw [← NL.phK_emb _ _ i h y, ← D.naut.iota_LL i y]
    exact congrArg (fun f : FractionRing (D.nd.O i) →+* ℂ => f (D.nd.embK i y)) hφK
  let κ : PlE D.host → ℕ → FractionRing (NL.B.Oc (D.nd.j i) (D.nd.w i)) := fun v k =>
    algebraMap _ _ (NL.phO _ _ i h (aF v k))
  have hκ : ∀ v k, SplitOut D.nd i v → 1 ≤ k → k ≤ D.R.nV → φ (κ v k) = lamF v k := by
    intro v k hv hk1 hk2
    simp only [κ, hφalg]
    rw [← hiotaC]
    exact (haF v k ⟨hv, hk1, hk2⟩).1
  obtain ⟨e, hene, he⟩ := GlobalTheory.T.complexHeckeEigenvector_descends_to_coefficientField D M NL.B (D.nd.j i) (D.nd.w i) (D.nd.mu i) (D.nd.j_range i).1
    (D.nd.j_range i).2 (D.nd.mu_w i) φ hφ κ y0 hy0ne (by
      intro v k hvk
      obtain ⟨hv, hk1, hk2⟩ := (Formalism.L2.genAt_iff NL h v k).2 hvk
      obtain ⟨s, ϖ, hc, hu⟩ := GlobalTheory.T.splitEx_every_datum D v hv.1
      have hbad : s.v ∉ Formalism.L2.badPl D i := not_bad_of_genAt NL _ _ i h v k s hvk hc
      have hfin := GlobalTheory.T.finite_cosets_heckeSet_at_splitPlace_outside_level D.host.E D.R.nV (M.loc i).J (M.loc i).χ (Formalism.L2.badPl D i) (HT.J_hyp i)
        s ϖ k hbad hu
      refine ⟨s, ϖ, hc, hu, ?_, ?_⟩
      · intro c f f'
        show Formalism.L2.NG.tN (M.loc i).J s ϖ k (c • f + f') =
          c • Formalism.L2.NG.tN (M.loc i).J s ϖ k f + Formalism.L2.NG.tN (M.loc i).J s ϖ k f'
        simp only [Formalism.L2.NG.tN]
        rw [heckeD_add _ _ _ _ hfin c f f', smul_add, smul_comm]
      · rw [hκ v k hv hk1 hk2]
        have e3 := (Classical.choose_spec (hyp P v hv)).2 k s ϖ hc hu hk1 hk2 y0 hy0
        rw [← hlamF v hv] at e3
        exact e3)
  have hinjK : Function.Injective (algebraMap (NL.B.Oc (D.nd.j i) (D.nd.w i))
      (FractionRing (NL.B.Oc (D.nd.j i) (D.nd.w i)))) := IsFractionRing.injective _ _
  obtain ⟨ψ, hψ, hψW⟩ := pt_of_eigvec (Formalism.L2.heckeGens NL.B (D.nd.j i) (D.nd.w i)) e hene hinjK (by
    rintro _ ⟨v, k, hvk, rfl⟩
    exact ⟨NL.phO _ _ i h (aF v k), he v k hvk⟩)
  have hψv : ∀ v k (hvk : Formalism.L2.GenAt D (D.what₂.places.resChar (D.nd.w i)) (NL.B.Qc (D.nd.j i) (D.nd.w i)) v k),
      ψ ⟨NL.B.hK _ _ v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ = NL.phO _ _ i h (aF v k) := by
    intro v k hvk
    apply hinjK
    have h1 := hψ ⟨NL.B.hK _ _ v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩
    have h2 := he v k hvk
    change NL.B.hK _ _ v k e = _ at h1
    rw [h2] at h1
    exact (smul_left_injective _ hene h1).symm
  have hcls : Formalism.L2.NCov.cls ψ = NL.mx _ _ i := by
    refine (cls_eq_of_residue _ ψ (NL.ptX _ _ i h x).1 ?_).trans (NL.ptX _ _ i h x).2.1
    rintro _ ⟨v, k, hvk, rfl⟩
    rw [hψv v k hvk, ← NL.ptX_hT _ _ i h x v k hvk]
    obtain ⟨hv, hk1, hk2⟩ := (Formalism.L2.genAt_iff NL h v k).2 hvk
    exact residue_map_equiv (NL.phO _ _ i h) (haF v k ⟨hv, hk1, hk2⟩).2
  have hW : Formalism.L2.NCov.W (Formalism.L2.heckeAlg NL.B _ _) (Formalism.L2.NCov.pt ψ) ≠ ⊥ := by
    intro h0
    apply hene
    have h3 := hψW
    rw [h0] at h3
    exact (Submodule.mem_bot _).1 h3
  refine ⟨(NL.ptX _ _ i h).symm ⟨ψ, hcls, hW⟩, (AV.ptV i P _).2 ?_⟩
  intro v k s ϖ hv hc hu hk1 hk2 y hy
  have hvk := (Formalism.L2.genAt_iff NL h v k).1 ⟨hv, hk1, hk2⟩
  have e1 := (Classical.choose_spec (hyp P v hv)).2 k s ϖ hc hu hk1 hk2 y hy
  rw [← hlamF v hv] at e1
  rw [e1]
  congr 1
  show lamF v k = iotaO D.nd D.naut i _
  rw [hiotaC, NL.ptX_hT _ _ i h _ v k hvk, Equiv.apply_symm_apply]
  show lamF v k = NL.iotaC _ _ (ψ ⟨NL.B.hK _ _ v k, _⟩)
  rw [hψv v k hvk, ← hiotaC]
  exact (haF v k ⟨hv, hk1, hk2⟩).1.symm

end GlobalTheory.PtLocalEig
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalSeriesAppendEquivParabolicProductStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prinSeries_append_isSubquotient_prod₂ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (ψ₁ : Fin r → kˣ →* ℂˣ) (ψ₂ : Fin t → kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (A : Representation ℂ (GL (Fin r) k) V) (B : Representation ℂ (GL (Fin t) k) W), Nonempty (A.Equiv (prinSeries ψ₁)) → Nonempty (B.Equiv (prinSeries ψ₂)) → IsSubquotient (prinSeries (Fin.append ψ₁ ψ₂)) (prod₂ A B) := by
  first | exact @GlobalTheory.SmGL.PrinProd.prinSeries_append | exact GlobalTheory.SmGL.PrinProd.prinSeries_append | (intros; apply GlobalTheory.SmGL.PrinProd.prinSeries_append <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SegmentSumTempered
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitaryPrecedes

theorem not_precedes_of_unitary : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ Δ Δ' : Segment (w.adicCompletion E), (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).eig φ, ‖α‖ = 1) → (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ ((rc Δ'.first).lpTw (((Δ'.len : ℝ) - 1) / 2)).eig φ, ‖α‖ = 1) → ¬ Δ.Precedes Δ' := by
  intro E Ω _ _ _ _ _ A w h rc hrc Δ Δ' hΔ hΔ' hP
  obtain ⟨a, ha, ε, -, H⟩ := hrc
  obtain ⟨hL, j, hj, hfirst⟩ := hP
  have hy' : rc Δ'.first = (rc Δ.first).lpTw (j : ℝ) := by
    rw [hfirst, ← H.nu_eq]
    norm_cast
  have hdeg : deg (frob h) = 1 := deg_frob
  have hcard : Multiset.card ((rc Δ.first).eig (frob h)) = Δ.d := by
    rw [WD.card_eig, H.dim]
    rfl
  obtain ⟨β, hβ⟩ := Multiset.card_pos_iff_exists_mem.1 (hcard ▸ Δ.d_pos)
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  set q : ℝ := ((normV w : ℕ) : ℝ) with hqdef
  have hn : ∀ s : ℝ, ‖((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)‖ = q ^ s := by
    intro s
    rw [← coe_qPow, norm_qPow]
  have h1 := hΔ (frob h) hdeg (β * ((normV w : ℕ) : ℂ) ^ (((((Δ.len : ℝ) - 1) / 2 : ℝ)) : ℂ))
    (by rw [GlobalTheory.RowTie.EigTwist.eig_lpTw _ hdeg]; exact Multiset.mem_map_of_mem _ hβ)
  have h2 := hΔ' (frob h) hdeg (β * ((normV w : ℕ) : ℂ) ^ (((j : ℕ) : ℝ) : ℂ) *
      ((normV w : ℕ) : ℂ) ^ (((((Δ'.len : ℝ) - 1) / 2 : ℝ)) : ℂ))
    (by
      rw [hy', GlobalTheory.RowTie.EigTwist.eig_lpTw _ hdeg, GlobalTheory.RowTie.EigTwist.eig_lpTw _ hdeg]
      exact Multiset.mem_map_of_mem _ (Multiset.mem_map_of_mem _ hβ))
  rw [norm_mul, hn] at h1
  rw [norm_mul, norm_mul, hn, hn] at h2
  have hb : ‖β‖ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have heq : q ^ (((Δ.len : ℝ) - 1) / 2) = q ^ (((j : ℕ) : ℝ) + (((Δ'.len : ℝ) - 1) / 2)) := by
    rw [Real.rpow_add (by linarith)]
    apply mul_left_cancel₀ hb
    rw [h1, ← mul_assoc, h2]
  have hexp : ((Δ.len : ℝ) - 1) / 2 = ((j : ℕ) : ℝ) + (((Δ'.len : ℝ) - 1) / 2) := by
    rcases lt_trichotomy (((Δ.len : ℝ) - 1) / 2) (((j : ℕ) : ℝ) + (((Δ'.len : ℝ) - 1) / 2)) with hlt | heq' | hgt
    · exact absurd heq (Real.rpow_lt_rpow_of_exponent_lt hq hlt).ne
    · exact heq'
    · exact absurd heq (Real.rpow_lt_rpow_of_exponent_lt hq hgt).ne'
  have hlen : Δ.len = Δ'.len + 2 * j := by
    have : (Δ.len : ℝ) = Δ'.len + 2 * j := by linarith
    exact_mod_cast this
  apply hL.2.2
  intro x hx
  rw [Segment.mem_carrier] at hx ⊢
  obtain ⟨b, hb', rfl⟩ := hx
  refine ⟨j + b, by omega, ?_⟩
  rw [hfirst, IrrGL.nu_nu]
  push_cast
  rfl

end GlobalTheory.UnitaryPrecedes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOneAddSkewHermitianMulLattice
section
open Matrix

noncomputable section

namespace GlobalTheory.SelfDualUnip

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem cT_add' (σ : L →+* L) {n : ℕ} (X Y : Matrix (Fin n) (Fin n) L) :
    Formalism.UG.cT σ (X + Y) = Formalism.UG.cT σ X + Formalism.UG.cT σ Y := by
  unfold Formalism.UG.cT; ext i j; simp

theorem det_cT (σ : L →+* L) {n : ℕ} (X : Matrix (Fin n) (Fin n) L) :
    (Formalism.UG.cT σ X).det = σ X.det := by
  unfold Formalism.UG.cT; rw [Matrix.det_transpose, RingHom.map_det]; rfl

theorem cT_int (σ : L →+* L) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {n : ℕ} {X : Matrix (Fin n) (Fin n) L}
    (hX : ∀ i j, X i j ∈ Formalism.UG.intL L) (i j : Fin n) : Formalism.UG.cT σ X i j ∈ Formalism.UG.intL L := by
  have h := hX j i
  rw [GlobalTheory.Hk3.mem_intL_iff] at h ⊢
  show Valued.v (σ (X j i)) ≤ 1
  rw [hσ]; exact h

theorem lift_int {n : ℕ} {X : Matrix (Fin n) (Fin n) L} (hX : ∀ i j, X i j ∈ Formalism.UG.intL L) :
    ∃ X' : Matrix (Fin n) (Fin n) (Formalism.UG.intL L), X'.map (Formalism.UG.intL L).subtype = X :=
  ⟨fun i j => ⟨X i j, hX i j⟩, by ext i j; rfl⟩

theorem v_det_eq_one {n : ℕ} {M N : Matrix (Fin n) (Fin n) L} (hM : ∀ i j, M i j ∈ Formalism.UG.intL L)
    (hN : ∀ i j, N i j ∈ Formalism.UG.intL L) (hMN : M * N = 1) : Valued.v M.det = 1 := by
  have hd : Valued.v M.det * Valued.v N.det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, hMN, Matrix.det_one, map_one]
  obtain ⟨M', rfl⟩ := lift_int hM
  obtain ⟨N', rfl⟩ := lift_int hN
  have hdM : (M'.map (Formalism.UG.intL L).subtype).det = (Formalism.UG.intL L).subtype M'.det :=
    (RingHom.map_det _ _).symm
  have hdN : (N'.map (Formalism.UG.intL L).subtype).det = (Formalism.UG.intL L).subtype N'.det :=
    (RingHom.map_det _ _).symm
  have hM1 : Valued.v (M'.map (Formalism.UG.intL L).subtype).det ≤ 1 := by
    rw [hdM]; exact (M'.det).2
  have hN1 : Valued.v (N'.map (Formalism.UG.intL L).subtype).det ≤ 1 := by
    rw [hdN]; exact (N'.det).2
  by_contra hne
  have hlt := lt_of_le_of_ne hM1 hne
  have := mul_lt_one_of_lt_of_le hlt hN1
  rw [hd] at this
  exact lt_irrefl _ this

theorem int_of_left_inv {n : ℕ} {G X : Matrix (Fin n) (Fin n) L} (hG : ∀ i j, G i j ∈ Formalism.UG.intL L)
    (hd : Valued.v G.det = 1) (hXG : X * G = 1) : ∀ i j, X i j ∈ Formalism.UG.intL L := by
  obtain ⟨G', rfl⟩ := lift_int hG
  have hdG : (G'.map (Formalism.UG.intL L).subtype).det = (Formalism.UG.intL L).subtype G'.det :=
    (RingHom.map_det _ _).symm
  have hne : (G'.map (Formalism.UG.intL L).subtype).det ≠ 0 := by
    intro h; rw [h, map_zero] at hd; exact zero_ne_one hd
  have hinv : ((G'.map (Formalism.UG.intL L).subtype).det)⁻¹ ∈ Formalism.UG.intL L := by
    rw [GlobalTheory.Hk3.mem_intL_iff, map_inv₀, hd, inv_one]
  have hu : IsUnit G'.det := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, ?_⟩
    apply Subtype.ext
    show (Formalism.UG.intL L).subtype G'.det * ((G'.map (Formalism.UG.intL L).subtype).det)⁻¹ = 1
    rw [← hdG]; exact mul_inv_cancel₀ hne
  have hGY : G'.map (Formalism.UG.intL L).subtype * (G'⁻¹).map (Formalism.UG.intL L).subtype = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv G' hu, Matrix.map_one _ (map_zero _) (map_one _)]
  have hX : X = (G'⁻¹).map (Formalism.UG.intL L).subtype := by
    calc X = X * (G'.map (Formalism.UG.intL L).subtype * (G'⁻¹).map (Formalism.UG.intL L).subtype) := by
          rw [hGY, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hXG, Matrix.one_mul]
  intro i j
  rw [hX]; exact (G'⁻¹ i j).2

theorem selfDual_mul_of_skew : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L), (∀ x, Valued.v (σ x) = Valued.v x) →
  ∀ (n : ℕ) (JS a k : GL (Fin n) L) (E : Matrix (Fin n) (Fin n) L),
  (∀ i j, (JS : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.HoweG.SelfDual σ JS a →
  Formalism.UG.cT σ E * (JS : Matrix (Fin n) (Fin n) L) = -((JS : Matrix (Fin n) (Fin n) L) * E) → (∀ i j, E i j ∈ Formalism.UG.intL L) →
  (∀ i j, (E * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) → (k : Matrix (Fin n) (Fin n) L) = 1 + E →
  (∀ i j, ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) →
  GlobalTheory.Hk3.HoweG.SelfDual σ JS (k * a) := by
  intro L _ _ σ hσ n JS a k E hJ ha hE hEint hEa hk hki
  obtain ⟨hG0, hX0⟩ := ha

  have hKint : ∀ i j, (k : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
    intro i j
    rw [hk, Matrix.add_apply, Matrix.one_apply]
    refine (Formalism.UG.intL L).add_mem ?_ (hEint i j)
    split_ifs
    · exact (Formalism.UG.intL L).one_mem
    · exact (Formalism.UG.intL L).zero_mem
  have hE' : ∀ X : Matrix (Fin n) (Fin n) L, Formalism.UG.cT σ E * ((JS : Matrix (Fin n) (Fin n) L) * X) =
      -((JS : Matrix (Fin n) (Fin n) L) * (E * X)) := by
    intro X; rw [← Matrix.mul_assoc, hE, Matrix.neg_mul, Matrix.mul_assoc]

  have hGeq : Formalism.UG.cT σ ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) *
      (JS : Matrix (Fin n) (Fin n) L) * ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) =
      Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L) +
      Formalism.UG.cT σ (E * (a : Matrix (Fin n) (Fin n) L)) * (JS : Matrix (Fin n) (Fin n) L) *
        (E * (a : Matrix (Fin n) (Fin n) L)) := by
    rw [hk, Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_add', Formalism.UG.cT_one]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, hE',
      Matrix.mul_neg]
    abel
  have hGint : ∀ i j, (Formalism.UG.cT σ ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) *
      (JS : Matrix (Fin n) (Fin n) L) * ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L))) i j ∈
      Formalism.UG.intL L := by
    intro i j
    rw [hGeq, Matrix.add_apply]
    exact (Formalism.UG.intL L).add_mem (hG0 i j)
      (GlobalTheory.Hk3.matMul_int (GlobalTheory.Hk3.matMul_int (cT_int σ hσ hEa) hJ) hEa i j)

  have hK1 : Valued.v (k : Matrix (Fin n) (Fin n) L).det = 1 := v_det_eq_one hKint hki k.mul_inv
  have hX0G0 : Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L) *
      (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        Formalism.UG.cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) = 1 := by
    have e3 : Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
      rw [← Formalism.UG.cT_mul, a.inv_mul, Formalism.UG.cT_one]
    calc _ = Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * ((JS : Matrix (Fin n) (Fin n) L) *
          (((a : Matrix (Fin n) (Fin n) L) * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) *
          (((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          Formalism.UG.cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)))) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [a.mul_inv, Matrix.one_mul, ← Matrix.mul_assoc (JS : Matrix (Fin n) (Fin n) L), JS.mul_inv,
          Matrix.one_mul, e3]
  have hG01 := v_det_eq_one hG0 hX0 hX0G0
  have hdet : Valued.v (Formalism.UG.cT σ ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) *
      (JS : Matrix (Fin n) (Fin n) L) * ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L))).det = 1 := by
    have : (Formalism.UG.cT σ ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) *
        (JS : Matrix (Fin n) (Fin n) L) * ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L))).det =
        σ (k : Matrix (Fin n) (Fin n) L).det * (k : Matrix (Fin n) (Fin n) L).det *
        (Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)).det := by
      simp only [Matrix.det_mul, det_cT, map_mul]; ring
    rw [this, map_mul, map_mul, hσ, hK1, hG01]; simp

  have hXG : (((k * a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      Formalism.UG.cT σ (((k * a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      (Formalism.UG.cT σ ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) *
      (JS : Matrix (Fin n) (Fin n) L) * ((k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L))) = 1 := by
    have hka : ((k * a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        (k : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L) := Units.val_mul k a
    rw [← hka]
    have e3 : Formalism.UG.cT σ (((k * a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        Formalism.UG.cT σ ((k * a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
      rw [← Formalism.UG.cT_mul, (k * a).mul_inv, Formalism.UG.cT_one]
    calc _ = (((k * a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          ((Formalism.UG.cT σ (((k * a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          Formalism.UG.cT σ ((k * a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) *
          ((JS : Matrix (Fin n) (Fin n) L) * ((k * a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)))) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e3, Matrix.one_mul, ← Matrix.mul_assoc ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L), JS.inv_mul, Matrix.one_mul, (k * a).inv_mul]
  refine ⟨?_, int_of_left_inv hGint hdet hXG⟩
  intro i j
  rw [Units.val_mul]
  exact hGint i j

end GlobalTheory.SelfDualUnip
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SkewConjGramSigmaConjTransposeTraceIdentity
section
open Matrix

namespace GlobalTheory

theorem skewConj_cT_mul_and_trace :
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L), (∀ x, σ (σ x) = x) →
  ∀ (n r : ℕ) (JS : GL (Fin n) L) (M : Matrix (Fin n) (Fin r) L) (Γ : Matrix (Fin r) (Fin r) L),
  (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) → (∀ k j, σ (Γ k j) = - Γ j k) →
  Formalism.UG.cT σ (M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) * (JS : Matrix (Fin n) (Fin n) L) = -((JS : Matrix (Fin n) (Fin n) L) * (M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L))) ∧
  ∀ (n' : ℕ) (JT : GL (Fin n') L) (y : Matrix (Fin n') (Fin n) L),
    Matrix.trace ((M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ y * (JT : Matrix (Fin n') (Fin n') L) * y) =
      Matrix.trace (Γ * (Formalism.UG.cT σ (y * M) * (JT : Matrix (Fin n') (Fin n') L) * (y * M))) := by
  intro L _ _ σ hσ n r JS M Γ hJ hΓ
  have hmul : ∀ {a b c : ℕ} (A : Matrix (Fin a) (Fin b) L) (B : Matrix (Fin b) (Fin c) L),
      Formalism.UG.cT σ (A * B) = Formalism.UG.cT σ B * Formalism.UG.cT σ A := by
    intro a b c A B
    simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have hcc : Formalism.UG.cT σ (Formalism.UG.cT σ M) = M := by
    ext i j
    simp [Formalism.UG.cT, hσ]
  have hJ' : Formalism.UG.cT σ (JS : Matrix (Fin n) (Fin n) L) = JS := by
    ext i j
    simp [Formalism.UG.cT, hJ]
  have hΓ' : Formalism.UG.cT σ Γ = -Γ := by
    ext i j
    simp [Formalism.UG.cT, hΓ]
  refine ⟨?_, ?_⟩
  · rw [hmul, hmul, hmul, hcc, hJ', hΓ']
    simp only [Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg]
  · intro n' JT y
    rw [hmul, Matrix.mul_assoc (M * Γ * Formalism.UG.cT σ M), Units.mul_inv, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm M]
    simp only [Matrix.mul_assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmithNormalFormDiscreteValuationFieldStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smithNormalForm_discreteValuationField : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (m n : ℕ) (M : Matrix (Fin m) (Fin n) L),
    ∃ (P P' : Matrix (Fin m) (Fin m) L) (Q Q' : Matrix (Fin n) (Fin n) L) (d : Fin m → L),
      (∀ i j, P i j ∈ Formalism.UG.intL L) ∧ (∀ i j, P' i j ∈ Formalism.UG.intL L) ∧
      (∀ i j, Q i j ∈ Formalism.UG.intL L) ∧ (∀ i j, Q' i j ∈ Formalism.UG.intL L) ∧ P * P' = 1 ∧ Q * Q' = 1 ∧
      M = P * Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0) * Q := by
  first | exact @GlobalTheory.SmithValued.smith_valued | exact GlobalTheory.SmithValued.smith_valued | (intros; apply GlobalTheory.SmithValued.smith_valued <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitHeckeElementLabelZerosThenNegOnesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_hecke_element_label_zeros_then_neg_ones : ∀ {D : D7} (V : HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i : ok × ℕ) (x : Bridge.Gf V), (i.2 ≤ V.rank → isTEnv V pl ok i x → IsLabElt V (pl i.1) (splitLab V.rank i.2) x) ∧ (isLocEnv V pl ok i x → IsLocElt V (pl i.1) x) ∧ (splitLab V.rank i.2).Pairwise (fun a b => b ≤ a) := by
  first | exact @GlobalTheory.Hk3Split.isLabElt_of_isTEnv | exact GlobalTheory.Hk3Split.isLabElt_of_isTEnv | (intros; apply GlobalTheory.Hk3Split.isLabElt_of_isTEnv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesPropertiesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_levels_good_primes_properties : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.Q A.μ0 = ∅ ∧ (∀ t P, Good R t P → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ Good R t (conjPl P) ∧ Good R A.μ0 P) ∧ (∀ SF, IsSF R SF → ∀ P, OffS D SF P ↔ Good R A.μ0 P) ∧ (R.IsFam → ∀ t, ∀ P ∈ A.ok t, Good R t (R.pl P) ∧ conjPl (R.pl P) ≠ R.pl P ∧ A.q P = Ideal.absNorm (R.pl P).asIdeal) := by
  first | exact @GlobalTheory.GoodPrimes.good_primes | exact GlobalTheory.GoodPrimes.good_primes | (intros; apply GlobalTheory.GoodPrimes.good_primes <;> assumption)
end

