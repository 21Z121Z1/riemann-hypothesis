import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0001
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0263
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0271
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualBoundAdmissible

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrthKerEqRangeAdjoint
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

noncomputable section

namespace GlobalTheory.EtaJoin.TypeSum

theorem orth_ker_eq_range_adjoint {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (A : V →ₗ[ℂ] W) : (LinearMap.ker A)ᗮ = LinearMap.range (LinearMap.adjoint A) := by
  have h : (LinearMap.range (LinearMap.adjoint A))ᗮ = LinearMap.ker A := by
    ext x
    simp only [Submodule.mem_orthogonal, LinearMap.mem_range, LinearMap.mem_ker, forall_exists_index,
      forall_apply_eq_imp_iff, LinearMap.adjoint_inner_left]
    constructor
    · intro hx
      exact ext_inner_left ℂ (fun y => by rw [hx y, inner_zero_right])
    · intro hx y
      rw [hx, inner_zero_right]
  rw [← h, Submodule.orthogonal_orthogonal]

variable {D : D7}

def eqvMt {μ μ' : D.what₂.Tup} {j j' : ℕ} (hμ : μ' = μ) (hj : j' = j) :
    D.what₂.Mt μ' j' ≃ₗ[ℂ] D.what₂.Mt μ j := by
  subst hμ; subst hj; exact LinearEquiv.refl ℂ _

theorem map_eqvMt_self {μ : D.what₂.Tup} {j : ℕ} (hμ : μ = μ) (hj : j = j) (V : Submodule ℂ (D.what₂.Mt μ j)) :
    V.map (eqvMt hμ hj).toLinearMap = V :=
  Submodule.map_id V

theorem map_eqvMt_thetaT_isot {μ μ' : D.what₂.Tup} {j j' : ℕ} (hμ : μ' = μ) (hj : j' = j) (σ : D.what₂.FT) :
    ((D.what₂.isot j' σ).map (D.what₂.thetaT μ' j')).map (eqvMt hμ hj).toLinearMap =
      (D.what₂.isot j σ).map (D.what₂.thetaT μ j) := by
  subst hμ; subst hj; exact map_eqvMt_self _ _ _

theorem map_eqvMt_range_thetaT {μ μ' : D.what₂.Tup} {j j' : ℕ} (hμ : μ' = μ) (hj : j' = j) :
    (LinearMap.range (D.what₂.thetaT μ' j')).map (eqvMt hμ hj).toLinearMap =
      LinearMap.range (D.what₂.thetaT μ j) := by
  subst hμ; subst hj; exact map_eqvMt_self _ _ _

theorem isoTyp_eq_of_isoRep {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type}
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) {S S' : Submodule ℂ (GAf L n → W)}
    (hS : ∀ h, ∀ f ∈ S, NG.rt L n h f ∈ S) (h : NG.IsoRep S S') : NG.isoTyp ρ S = NG.isoTyp ρ S' := by
  unfold NG.isoTyp
  congr 1
  ext T
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (h.symm hS).trans h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h.trans h2⟩⟩

variable {M : MtFam D}

theorem typeV_of_transport (A : AVTied D M) (i : D.nd.Loc) {μ' : D.what₂.Tup} {j' : ℕ}
    (hμ : μ' = D.nd.mu i) (hj : j' = D.nd.j i) (h1 : 1 ≤ j') (h2 : j' ≤ D.R.m)
    (S' : Submodule ℂ (GAf D.host.E D.R.nV → (M μ' j' h1 h2).wt.W))
    (hirr : NG.IsIrrRep (M μ' j' h1 h2).wt.ρ S')
    (hne : (NG.isoTyp (M μ' j' h1 h2).wt.ρ S').comap (M μ' j' h1 h2).real ≠ ⊥) :
    ∃ P, ((NG.isoTyp (M μ' j' h1 h2).wt.ρ S').comap (M μ' j' h1 h2).real).map (eqvMt hμ hj).toLinearMap =
      D.naut.typeV i P := by
  subst hμ; subst hj
  obtain ⟨P, hP⟩ := A.surj i S' hirr hne
  refine ⟨P, ?_⟩
  have e := isoTyp_eq_of_isoRep (M.loc i).wt.ρ (A.irr i P).1.stable hP
  rw [map_eqvMt_self, A.typeV i P, e]
  rfl

theorem eig_of_transport (A : AVTied D M) (i : D.nd.Loc) (P : D.naut.AV i) (x : D.nd.X i)
    (hx : D.naut.ptV i P = some x) {μ' : D.what₂.Tup} {j' : ℕ}
    (hμ : μ' = D.nd.mu i) (hj : j' = D.nd.j i) (h1 : 1 ≤ j') (h2 : j' ≤ D.R.m)
    (V : Submodule ℂ (D.what₂.Mt μ' j')) (hV : V.map (eqvMt hμ hj).toLinearMap = D.naut.typeV i P)
    (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E))
    (hw : SplitOut D.nd i w) (hc : IsConjPl D.host w s.w) (hu : IsUnif D.host.E s.v ϖ) (k1 : 1 ≤ k)
    (k2 : k ≤ D.R.nV) (c : ℂ)
    (hV' : ∀ y ∈ V, NG.tN (M μ' j' h1 h2).J s ϖ k ((M μ' j' h1 h2).real y) = c • (M μ' j' h1 h2).real y) :
    c = iotaOC D i ((D.nd.hT i w k : D.nd.X i → D.nd.O i) x) := by
  subst hμ; subst hj
  rw [map_eqvMt_self] at hV
  subst hV
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (D.naut.typeV_ne i P)
  have e1 := A.eigen i P x hx w k s ϖ hw hc hu k1 k2 y hy
  have e2 := hV' y hy
  have hr : (M.loc i).real y ≠ 0 := fun h => hy0 ((M.loc i).real_inj (h.trans (map_zero _).symm))
  exact smul_left_injective ℂ hr (e2.symm.trans e1)

end GlobalTheory.EtaJoin.TypeSum

namespace GlobalTheory.EtaJoin.TypeSum

theorem main : ∀ (D : D7) (M : MtFam D) (i : D.nd.Loc), HeckeTied D M → AVTied D M → SplitUnif D → TypeOrth D i →
    ThetaCut D (D.nd.mu i) (D.nd.j i) → Rows.IsotInternal D.what₂ → Formalism.MainNotions.SumRepresentations.ConclusionZ D →
    (∀ σ, D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ ∧ ∃ i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i),
      Formalism.MainNotions.N.HG D.nd D.naut i' ∧ Formalism.MainNotions.N.AtM D.nd D.naut i' σ) → ZSpec D i := by
  intro D M i HT A SU TO TC II PZ EX
  have hZ0 : Idx.Z0 D (D.nd.mu i) (D.nd.j i) = LinearMap.range (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) := by
    unfold Idx.Z0
    rw [orth_ker_eq_range_adjoint]
    exact inf_eq_left.2 TC
  have hmu : ∀ i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i), D.nd.mu i' = D.nd.mu i := fun i' hi' => by
    rw [D.nd.mu_w, D.nd.mu_w, ((D.nd.locs_mem _ _ i').1 hi').2]
  let G : Set (D.naut.AV i) := {P | ∃ i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i), ∃ x' ∈ Formalism.MainNotions.N.ZgoodN D.nd D.naut i',
    ∃ P' : D.naut.AV i', D.naut.ptV i' P' = some x' ∧ ∃ (hμ : D.nd.mu i' = D.nd.mu i) (hj : D.nd.j i' = D.nd.j i),
      (D.naut.typeV i' P').map (eqvMt hμ hj).toLinearMap = D.naut.typeV i P}

  have hin : ∀ P ∈ G, D.naut.typeV i P ≤ LinearMap.range (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) := by
    rintro P ⟨i', hi', x', hx', P', hP', hμ, hj, he⟩
    have hZ := (PZ i' ⟨x', hx'⟩).2.1
    have h1 : D.naut.typeV i' P' ≤ LinearMap.range (D.what₂.thetaT (D.nd.mu i') (D.nd.j i')) := by
      refine le_trans ?_ (LinearMap.map_le_range (f := D.what₂.thetaT (D.nd.mu i') (D.nd.j i'))
        (p := Formalism.MainNotions.N.goodPartM D.nd D.naut i'))
      rw [hZ]
      refine le_trans ?_ (le_biSup (fun x => Formalism.MainNotions.N.eigC D.nd D.naut i' x) hx')
      unfold Formalism.MainNotions.N.eigC
      exact le_biSup (fun Q => D.naut.typeV i' Q) (show P' ∈ {Q | D.naut.ptV i' Q = some x'} from hP')
    rw [← he, ← map_eqvMt_range_thetaT hμ hj]
    exact Submodule.map_mono h1

  have hsub : LinearMap.range (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) ≤ ⨆ P ∈ G, D.naut.typeV i P := by
    rw [LinearMap.range_eq_map, ← ((II (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2).submodule_iSup_eq_top),
      Submodule.map_iSup]
    refine iSup_le fun σ => ?_
    by_cases h0 : D.what₂.isot (D.nd.j i) σ = ⊥
    · rw [h0, Submodule.map_bot]; exact bot_le
    obtain ⟨hg, i', hi', hHG, hAt⟩ := EX σ h0
    have hj : D.nd.j i' = D.nd.j i := ((D.nd.locs_mem _ _ i').1 hi').1
    have hμ := hmu i' hi'
    have h1 : D.what₂.isot (D.nd.j i') σ ≤ Formalism.MainNotions.N.goodPartM D.nd D.naut i' :=
      le_biSup (fun τ => D.what₂.isot (D.nd.j i') τ) (show σ ∈ {τ | D.nd.goodRow τ ∧ Formalism.MainNotions.N.AtM D.nd D.naut i' τ} from ⟨hg, hAt⟩)
    have h2 := Submodule.map_mono (f := D.what₂.thetaT (D.nd.mu i') (D.nd.j i')) h1
    rw [(PZ i' hHG).2.1] at h2
    rw [← map_eqvMt_thetaT_isot hμ hj]
    refine le_trans (Submodule.map_mono h2) ?_
    rw [Submodule.map_le_iff_le_comap]
    refine iSup₂_le fun x' hx' => ?_
    unfold Formalism.MainNotions.N.eigC
    refine iSup₂_le fun P' hP' => ?_
    rw [← Submodule.map_le_iff_le_comap]
    have hne : (NG.isoTyp (M.loc i').wt.ρ (A.S i' P')).comap (M.loc i').real ≠ ⊥ := by
      rw [← A.typeV i' P']; exact D.naut.typeV_ne i' P'
    obtain ⟨P, hP⟩ := typeV_of_transport A i hμ hj (D.nd.j_range i').1 (D.nd.j_range i').2 (A.S i' P') (A.irr i' P') hne
    have hT : (D.naut.typeV i' P').map (eqvMt hμ hj).toLinearMap = D.naut.typeV i P := by
      rw [A.typeV i' P']; exact hP
    rw [hT]
    exact le_biSup (fun Q => D.naut.typeV i Q) (show P ∈ G from ⟨i', hi', x', hx', P', hP', hμ, hj, hT⟩)
  have hZG : LinearMap.range (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) = ⨆ P ∈ G, D.naut.typeV i P :=
    le_antisymm hsub (iSup₂_le hin)
  have hout : ∀ P, P ∉ G → D.naut.typeV i P ≤ (LinearMap.range (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)))ᗮ := by
    intro P hP
    rw [← Submodule.isOrtho_iff_le]
    apply Submodule.IsOrtho.symm
    rw [Submodule.isOrtho_iff_le, hZG]
    refine iSup₂_le fun Q hQ => ?_
    rw [← Submodule.isOrtho_iff_le]
    exact TO Q P (fun h => hP (h ▸ hQ))
  unfold ZSpec
  rw [hZ0]
  intro P
  refine ⟨(em (P ∈ G)).elim (fun h => Or.inl (hin P h)) (fun h => Or.inr (hout P h)), fun x hx => ⟨fun hg => ?_, fun hb => hout P ?_⟩⟩
  · exact hin P ⟨i, (D.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩, x, (D.Zgood_tie i x).1 hg, P, hx, rfl, rfl, map_eqvMt_self _ _ _⟩
  · rintro ⟨i', hi', x', hx', P', hP', hμ, hj, he⟩
    obtain ⟨hj', hw'⟩ := (D.nd.locs_mem _ _ i').1 hi'
    by_cases hii : i' = i
    · subst hii
      rw [map_eqvMt_self] at he
      have hPP : P' = P := by
        by_contra hne
        have hd : Disjoint (D.naut.typeV i' P') (D.naut.typeV i' P) := (D.naut.typeV_indep i').pairwiseDisjoint hne
        rw [he] at hd
        exact D.naut.typeV_ne i' P (disjoint_self.1 hd)
      subst hPP
      rw [hx] at hP'
      cases hP'
      exact hb ((D.Zgood_tie _ _).2 hx')
    · obtain ⟨φ, hφ⟩ := HT.sameO i i' hj'.symm hw'.symm
      obtain ⟨v, k, hv, hv', k1, k2, hunit⟩ := HT.sep i i' φ hφ hj'.symm hw'.symm (Ne.symm hii) x x'
      obtain ⟨s, ϖ, hc, hu⟩ := SU v hv.1
      have e := eig_of_transport A i P x hx hμ hj (D.nd.j_range i').1 (D.nd.j_range i').2 (D.naut.typeV i' P') he
        v k s ϖ hv hc hu k1 k2 _ (fun y hy => A.eigen i' P' x' hP' v k s ϖ hv' hc hu k1 k2 y hy)
      rw [hφ] at e
      have hinj : Function.Injective (iotaOC D i') := by
        intro a b h
        simp only [iotaOC, RingHom.coe_comp, Function.comp_apply] at h
        exact IsFractionRing.injective (D.nd.O i') (FractionRing (D.nd.O i'))
          ((D.naut.iotaQ i').injective ((D.naut.iotaQC i').injective h))
      rw [hinj e, sub_self] at hunit
      exact not_isUnit_zero hunit

end GlobalTheory.EtaJoin.TypeSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntRingHomContinuousOfPadicCoeff
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

namespace GlobalTheory

theorem padicInt_ringHom_continuous_of_padicCoeff : ∀ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [TopologicalSpace O], PadicCoeff p O → ∀ φ : ℤ_[p] →+* O, Continuous φ := by
  intro p _ O _ _ _ _ hO φ
  haveI := hO.ring
  refine continuous_of_continuousAt_zero φ ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨n, hn⟩ := (isAdic_iff.mp hO.adic).2 s hs
  have hball : Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-(n : ℤ))) ∈ nhds (0 : ℤ_[p]) := by
    apply Metric.closedBall_mem_nhds
    have : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    positivity
  refine Filter.mem_map.mpr (Filter.mem_of_superset hball ?_)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, PadicInt.norm_le_pow_iff_mem_span_pow] at hx
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  apply hn
  show φ (a * (p : ℤ_[p]) ^ n) ∈ ((IsLocalRing.maximalIdeal O) ^ n : Ideal O)
  rw [map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hO.p_mem n)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicValNatFinrankKs
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory.HubLoc

theorem padicValNat_finrank_Ks : ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), (∀ m : ℕ, 0 < m → padicValNat l (finrank ℚ_[l] ↥(Loc.Ks K m)) - padicValNat l (finrank ℚ_[l] ↥(Loc.Ks K 1)) = m - 1) ∧ (K.1 ≤ Loc.MaximalUnramifiedExtension l → padicValNat l (finrank ℚ_[l] ↥(Loc.Ks K 1)) - padicValNat l (finrank ℚ_[l] ↥K.1) = 0) := by
  intro l _ K
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hl1 : l - 1 ≠ 0 := by omega
  have hpow : ∀ n : ℕ, l ^ n ≠ 0 := fun n => pow_ne_zero n (by omega)

  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hle : Loc.K0 K ≤ K.1 := by unfold Loc.K0; exact inf_le_left
  haveI : FiniteDimensional ℚ_[l] ↥(Loc.K0 K) :=
    Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).injective
  have hk0 : finrank ℚ_[l] ↥(Loc.K0 K) ≠ 0 := Module.finrank_pos.ne'
  refine ⟨fun m hm => ?_, fun hK => ?_⟩
  ·
    rw [finrank_Ks_eq l K m hm, finrank_Ks_eq l K 1 one_pos,
      padicValNat.mul hk0 (Nat.mul_ne_zero (hpow _) hl1),
      padicValNat.mul hk0 (Nat.mul_ne_zero (hpow _) hl1),
      padicValNat.mul (hpow _) hl1, padicValNat.mul (hpow _) hl1,
      padicValNat.prime_pow, padicValNat.prime_pow]
    omega
  ·
    have heq : Loc.K0 K = K.1 := by unfold Loc.K0; exact inf_eq_left.mpr hK
    have hK1 : finrank ℚ_[l] ↥K.1 ≠ 0 := Module.finrank_pos.ne'
    have hv : padicValNat l (l - 1) = 0 :=
      padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
    rw [finrank_Ks_eq l K 1 one_pos, heq, padicValNat.mul hK1 (Nat.mul_ne_zero (hpow _) hl1),
      padicValNat.mul (hpow _) hl1, padicValNat.prime_pow, hv]
    omega

end GlobalTheory.HubLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalFormEqSumLocalisationProjections
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

noncomputable section

namespace GlobalTheory.NSideDecomp

theorem part_le_off' {O K V : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V]
    [Module O V] [IsScalarTower O K V] [IsLocalRing O] (T : Subalgebra O (Module.End K V)) {I J : Ideal T}
    (h : I ≠ J) : NCov.part T I ≤ NCov.off T J :=
  iSup₂_le fun ψ hψ => le_iSup₂_of_le (f := fun ψ (_ : NCov.cls ψ ≠ J) => NCov.W T (NCov.pt ψ)) ψ
    (by rw [hψ]; exact h) le_rfl

theorem iV_eq_sum_Psi : ∀ (D : D7) (M : MtFam D) (T : NormalizedLocalCompatibility D M) (j : ℕ) (w : D.what₂.places.Pl), 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → HeckeStdTw T.B → ∀ y : D.what₂.MtL (D.what₂.muTw w) j, T.B.iV j w y = ∑ i ∈ (D.nd.locs j w).attach, T.Psi j w i.1 i.2 (D.nd.prMt i.1 (castMtInv D i.2 y)) := by
  classical
  intro D M T j w h1 h2 hw hstd y
  obtain ⟨hfd, -⟩ := finrank_V T.B j w
  haveI := hfd
  obtain ⟨hS, hsplit, hint⟩ := gens_hypsTw T.B hstd h1 h2 (Or.inl hw)
  have hinj := IsFractionRing.injective (T.B.Oc j w) (FractionRing (T.B.Oc j w))
  rw [← sub_eq_zero]
  refine NCov.eq_zero_of_forall_mem_off hinj hS hsplit hint ((D.nd.locs j w).image (T.mx j w))
    (fun I hI => ?_) ?_
  · obtain ⟨i, hi, rfl⟩ := T.mx_all j w h1 h2 hw I hI
    exact Finset.mem_image_of_mem _ hi
  · intro I hI
    obtain ⟨i0, hi0, rfl⟩ := Finset.mem_image.1 hI
    rw [← Finset.add_sum_erase _ _ (Finset.mem_attach _ ⟨i0, hi0⟩), sub_add_eq_sub_sub]
    refine Submodule.sub_mem _ ?_ (Submodule.sum_mem _ fun i hi => ?_)
    · have e := T.Psi_pr j w i0 hi0 (castMtInv D hi0 y)
      rw [castMt_castMtInv] at e
      rw [← neg_sub]
      exact Submodule.neg_mem _ e
    · have hne : T.mx j w i.1 ≠ T.mx j w i0 := by
        intro e
        have := T.mx_inj j w i.2 hi0 e
        exact (Finset.mem_erase.1 hi).1 (Subtype.ext this)
      exact part_le_off' _ hne ((T.Psi_range j w i.1 i.2 _).2 ⟨_, rfl⟩)

end GlobalTheory.NSideDecomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionCyclotomicEndoEqFrobeniusLaurentStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_cyclotomic_endo_eq_frobenius_laurent : ∀ (l : ℕ) [Fact l.Prime] (O k : Type) [CommRing O] [Field k] [Algebra O k] [CharP k l] (φ₀ : O⟦X⟧ →ₐ[O] O⟦X⟧), φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ l - 1 → ∀ a : O⟦X⟧, ((PowerSeries.map (algebraMap O k) (φ₀ a) : k⟦X⟧) : k⸨X⸩) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.phiPi k l ((PowerSeries.map (algebraMap O k) a : k⟦X⟧) : k⸨X⸩) := by
  first | exact @GlobalTheory.RedPhiProof.red_phi | exact GlobalTheory.RedPhiProof.red_phi | (intros; apply GlobalTheory.RedPhiProof.red_phi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionMapPi0Statement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_map_pi0 : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) (l : ℕ) [Fact l.Prime] {k : Type} [Field k] [Algebra O k] [CharP k l], PD.p = l → ∀ e : {δ // δ ∈ W.DelF} ≃ {z : ℤ_[l] // z ^ (l - 1) = 1}, (∀ δ a, PowerSeries.map (algebraMap O k) (W.γ₀ δ.1 a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l (e δ).1 (PowerSeries.map (algebraMap O k) a)) → PowerSeries.map (algebraMap O k) W.π₀₁ = 1 + ∑ᶠ z : {z : ℤ_[l] // z ^ (l - 1) = 1}, GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.onePlusPow k l z.1 := by
  first | exact @GlobalTheory.RedFun.map_pi0 | exact GlobalTheory.RedFun.map_pi0 | (intros; apply GlobalTheory.RedFun.map_pi0 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualBoundOfBoundOnSets
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open GlobalTheory.IndefiniteRowSideFullHecke.ResidualBoundAdmissible

namespace GlobalTheory.TwSys.ResidualCompare

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem isConjPl_unique {P v v' : PlE D.host} (h : IsConjPl D.host P v) (h' : IsConjPl D.host P v') : v = v' := by
  apply HeightOneSpectrum.ext
  ext y
  obtain ⟨x, hx⟩ := (RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv).surjective y
  have hy : (y : D.host.E) = D.host.conj (x : D.host.E) := by
    rw [← hx]; rfl
  rw [← h x y hy, ← h' x y hy]

theorem exists_isQ {ι : Type} [Finite ι] (P : ι → PlE D.host) : ∃ Q, IsQ P Q := by
  have hf : (⋃ q, {v | Over (P q) v}).Finite := by
    refine Set.finite_iUnion fun q => ?_
    have h2 : {v | IsConjPl D.host (P q) v}.Subsingleton := fun _ h _ h' => isConjPl_unique h h'
    exact ((Set.finite_singleton (P q)).union h2.finite).subset fun v hv => hv
  exact ⟨hf.toFinset, fun v => by simp⟩

theorem isQ_unique {ι : Type} {P : ι → PlE D.host} {Q Q' : Finset (PlE D.host)} (h : IsQ P Q) (h' : IsQ P Q') :
    Q = Q' := Finset.ext fun v => (h v).trans (h' v).symm

theorem not_goodChar_one (i : X.Tw) {M : ℕ} (hM : 1 ≤ M) (P : PlE D.host) : ¬ GoodChar X i M P 1 := by
  intro h
  have : Fact (1 < X.l i ^ M) := ⟨Nat.one_lt_pow (by omega) (X.lPrime i).out.one_lt⟩
  obtain ⟨σ, -, hσ⟩ := h.2.2.2.2 P (Or.inl rfl) _ (N.plOm.2 P) (Multiplicative.ofAdd 1)
  have h1 : (0 : ZMod (X.l i ^ M)) = 1 := congrArg Multiplicative.toAdd hσ
  exact zero_ne_one h1

theorem addVal_le_zero_iff {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (x : O) :
    IsDiscreteValuationRing.addVal O x ≤ 0 ↔ IsUnit x := by
  rw [nonpos_iff_eq_zero, IsDiscreteValuationRing.addVal_eq_zero_iff]

variable (bkP : BKPh X)

def AtLevel₁ (i : X.Tw) (T : Set (X.Sig i)) (R n M : ℕ) : Prop :=
  ∀ H S d, AdmFam X i M H S d → ∀ z, IsTameInertiaElementAtTwistPrime X i z → ∀ (H' : Subgroup (GE N)), IsOpen (H' : Set (GE N)) → H'.Normal →
    ∀ A : Finset (PlE D.host), ∃ P : Fin R ⊕ Fin R → PlE D.host,
      SlopeTestRemainingChoices X i M A P (fun q => d (P q)) ∧ Steps X i M H' z P (fun q => d (P q)) ∧
      ∀ s ∈ T, ∀ Q, IsQ P Q → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M (Fin R ⊕ Fin R))),
        Computes bkP i s M (fun q => d (P q)) Q Φ → ∀ F, toLam X i M (Fin R ⊕ Fin R) F = Φ.det →
        ∃ m : Fin R ⊕ Fin R →₀ ℕ, m.degree ≤ n ∧ IsDiscreteValuationRing.addVal (X.O0 i) (F.coeff m) ≤ 0

def AtLevel₂ (i : X.Tw) (T : Set (X.Sig i)) (R n M : ℕ) : Prop :=
  ∀ (H : Subgroup (GE N)) (S : Finset (PlE D.host))
    (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))), AdmFam X i M H S d →
    ∀ z : GE N, IsTameInertiaElementAtTwistPrime X i z →
    ∀ H' : Subgroup (GE N), IsOpen (H' : Set (GE N)) → H'.Normal →
    ∀ A : Finset (PlE D.host),
      ∃ (P : Fin R ⊕ Fin R → PlE D.host) (Q : Finset (PlE D.host)),
        (∀ q, AdmPl H S (P q)) ∧
        SlopeTestRemainingChoices X i M A P (fun q => d (P q)) ∧
        Steps X i M H' z P (fun q => d (P q)) ∧
        IsQ P Q ∧
        ∀ s ∈ T, ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M (Fin R ⊕ Fin R))),
          Computes bkP i s M (fun q => d (P q)) Q Φ → OrdLE X i M (Fin R ⊕ Fin R) n Φ.det

theorem ordBound_zero_iff (i : X.Tw) : OrdBound bkP i 0 ↔
    ∀ T : Set (X.Sig i), (∀ s ∈ T, GalHyp bkP i s) → ∃ R n M₀ : ℕ, ∀ M, M₀ ≤ M → AtLevel₁ bkP i T R n M := Iff.rfl

theorem residualBoundOn_iff (i : X.Tw) (T : Set (X.Sig i)) : ResidualBoundOn bkP i T ↔
    (nu X i = 0 → (∀ s ∈ T, GalHyp bkP i s) →
      ∃ R : ℕ, ∀ M : ℕ, 4 * D.R.r * R + 1 < X.l i ^ M → AtLevel₂ bkP i T R (4 * D.R.r * R) M) := Iff.rfl

theorem atLevel₁_of_atLevel₂ {i : X.Tw} {T : Set (X.Sig i)} {R n M : ℕ} (h : AtLevel₂ bkP i T R n M) :
    AtLevel₁ bkP i T R n M := by
  intro H S d hd z hz H' ho hn A
  obtain ⟨P, Q, -, h2, h3, h4, h5⟩ := h H S d hd z hz H' ho hn A
  refine ⟨P, h2, h3, fun s hs Q' hQ' a Φ hΦ F hF => ?_⟩
  obtain rfl := isQ_unique h4 hQ'
  obtain ⟨m, hm, hu⟩ := h5 s hs a Φ hΦ F hF
  exact ⟨m, hm, (addVal_le_zero_iff _).2 hu⟩

theorem atLevel₂_of_atLevel₁ {i : X.Tw} {T : Set (X.Sig i)} {R n M : ℕ} (hM : 1 ≤ M) (h : AtLevel₁ bkP i T R n M) :
    AtLevel₂ bkP i T R n M := by
  classical
  intro H S d hd z hz H' ho hn A
  let d' : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M))) := fun P => if AdmPl H S P then d P else 1
  have hd' : AdmFam X i M H S d' := by
    refine ⟨hd.1, hd.2.1, hd.2.2.1, fun P h1 h2 h3 => ?_⟩
    have : d' P = d P := if_pos ⟨h1, h2, h3⟩
    rw [this]
    exact hd.2.2.2 P h1 h2 h3
  obtain ⟨P, h2, h3, h5⟩ := h H S d' hd' z hz H' ho hn A
  have hadm : ∀ q, AdmPl H S (P q) := by
    intro q
    by_contra hq
    have h6 : GoodChar X i M (P q) (d' (P q)) := h2.2.2 q
    have : d' (P q) = 1 := if_neg hq
    rw [this] at h6
    exact not_goodChar_one i hM _ h6
  have he : (fun q => d' (P q)) = fun q => d (P q) := funext fun q => if_pos (hadm q)
  rw [he] at h2 h3 h5
  obtain ⟨Q, hQ⟩ := exists_isQ P
  refine ⟨P, Q, hadm, h2, h3, hQ, fun s hs a Φ hΦ F hF => ?_⟩
  obtain ⟨m, hm, hu⟩ := h5 s hs Q hQ a Φ hΦ F hF
  exact ⟨m, hm, (addVal_le_zero_iff _).1 hu⟩

theorem atLevel_iff (i : X.Tw) (T : Set (X.Sig i)) (R n : ℕ) {M : ℕ} (hM : 1 ≤ M) :
    AtLevel₁ bkP i T R n M ↔ AtLevel₂ bkP i T R n M :=
  ⟨atLevel₂_of_atLevel₁ bkP hM, atLevel₁_of_atLevel₂ bkP⟩

theorem residual_bound_iff_free_level : ResidualBoundOddPrimes bkP ↔ ∀ (i : X.Tw) (T : Set (X.Sig i)), nu X i = 0 → (∀ s ∈ T, GalHyp bkP i s) →
    ∃ R n M₀ : ℕ, ∀ M, M₀ ≤ M → AtLevel₂ bkP i T R n M := by
  constructor
  · intro h i T hl hT
    obtain ⟨R, n, M₀, hM⟩ := (ordBound_zero_iff bkP i).1 (h i hl) T hT
    exact ⟨R, n, max M₀ 1, fun M hle =>
      atLevel₂_of_atLevel₁ bkP (le_trans (le_max_right _ _) hle) (hM M (le_trans (le_max_left _ _) hle))⟩
  · intro h i hl
    refine (ordBound_zero_iff bkP i).2 fun T hT => ?_
    obtain ⟨R, n, M₀, hM⟩ := h i T hl hT
    exact ⟨R, n, M₀, fun M hle => atLevel₁_of_atLevel₂ bkP (hM M hle)⟩

theorem residualBoundOn_iff_sharp (i : X.Tw) (T : Set (X.Sig i)) : ResidualBoundOn bkP i T ↔
    (nu X i = 0 → (∀ s ∈ T, GalHyp bkP i s) →
      ∃ R : ℕ, ∀ M : ℕ, 4 * D.R.r * R + 1 < X.l i ^ M → AtLevel₁ bkP i T R (4 * D.R.r * R) M) := by
  rw [residualBoundOn_iff]
  refine forall₂_congr fun _ _ => exists_congr fun R => forall₂_congr fun M hM => (atLevel_iff bkP i T R _ ?_).symm
  rcases Nat.eq_zero_or_pos M with rfl | h
  · simp at hM
  · exact h

theorem loose_of_residualBoundOn {i : X.Tw} {T : Set (X.Sig i)} (h : ResidualBoundOn bkP i T) (hl : nu X i = 0)
    (hT : ∀ s ∈ T, GalHyp bkP i s) : ∃ R n M₀ : ℕ, ∀ M, M₀ ≤ M → AtLevel₁ bkP i T R n M := by
  obtain ⟨R, hR⟩ := (residualBoundOn_iff_sharp bkP i T).1 h hl hT
  refine ⟨R, 4 * D.R.r * R, 4 * D.R.r * R + 1, fun M hM => hR M ?_⟩
  exact lt_of_le_of_lt hM (Nat.lt_pow_self (X.lPrime i).out.one_lt)

theorem residual_bound_of_bound_on_sets (h : ∀ (i : X.Tw) (T : Set (X.Sig i)), ResidualBoundOn bkP i T) : ResidualBoundOddPrimes bkP :=
  fun i hl => (ordBound_zero_iff bkP i).2 fun T hT => loose_of_residualBoundOn bkP (h i T) hl hT

theorem AtLevel₁.mono {i : X.Tw} {T T' : Set (X.Sig i)} {R n M : ℕ} (hT : T' ⊆ T) (h : AtLevel₁ bkP i T R n M) :
    AtLevel₁ bkP i T' R n M := by
  intro H S d hd z hz H' ho hn A
  obtain ⟨P, h2, h3, h5⟩ := h H S d hd z hz H' ho hn A
  exact ⟨P, h2, h3, fun s hs => h5 s (hT hs)⟩

theorem ordBound_of_residualBound (i : X.Tw) (hl : nu X i = 0) (hg : ∀ s, goodS bkP i s ↔ GalHyp bkP i s)
    (h : ResidualBound bkP i) : OrdBound bkP i 0 := by
  refine (ordBound_zero_iff bkP i).2 fun T hT => ?_
  obtain ⟨R, n, M₀, hM⟩ := loose_of_residualBoundOn bkP h hl fun s hs => (hg s).1 hs
  exact ⟨R, n, M₀, fun M hle => (hM M hle).mono bkP fun s hs => (hg s).2 (hT s hs)⟩

theorem good_rows_at_level_of_residual (h : ResidualBoundOddPrimes bkP) (i : X.Tw) (hl : nu X i = 0)
    (hg : ∀ s, goodS bkP i s → GalHyp bkP i s) :
    ∃ R n M₀ : ℕ, ∀ M, M₀ ≤ M → AtLevel₂ bkP i {s | goodS bkP i s} R n M :=
  (residual_bound_iff_free_level bkP).1 h i _ hl hg

theorem comparison :
    (∀ (i : X.Tw) (T : Set (X.Sig i)) (R n M : ℕ), 1 ≤ M → (AtLevel₁ bkP i T R n M ↔ AtLevel₂ bkP i T R n M)) ∧
    (ResidualBoundOddPrimes bkP ↔ ∀ (i : X.Tw) (T : Set (X.Sig i)), nu X i = 0 → (∀ s ∈ T, GalHyp bkP i s) →
      ∃ R n M₀ : ℕ, ∀ M, M₀ ≤ M → AtLevel₂ bkP i T R n M) ∧
    (∀ (i : X.Tw) (T : Set (X.Sig i)), ResidualBoundOn bkP i T ↔ (nu X i = 0 → (∀ s ∈ T, GalHyp bkP i s) →
      ∃ R : ℕ, ∀ M : ℕ, 4 * D.R.r * R + 1 < X.l i ^ M → AtLevel₁ bkP i T R (4 * D.R.r * R) M)) ∧
    ((∀ (i : X.Tw) (T : Set (X.Sig i)), ResidualBoundOn bkP i T) → ResidualBoundOddPrimes bkP) :=
  ⟨fun i T R n _ hM => atLevel_iff bkP i T R n hM, residual_bound_iff_free_level bkP, residualBoundOn_iff_sharp bkP,
    residual_bound_of_bound_on_sets bkP⟩

end GlobalTheory.TwSys.ResidualCompare

end
end

