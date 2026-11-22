import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0778
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1182
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0082
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogCutoffCoordinateHyperplanesPoincareBoun
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryPointOfLocalFamily
section
noncomputable section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.LocGlue

theorem entry_mem {E : Type} [Field E] [NumberField E] {n : ℕ} {v : HeightOneSpectrum (𝓞 E)}
    {g : GL (Fin n) (v.adicCompletion E)} (hg : g ∈ GlobalTheory.LFun.KGL v n) (i j : Fin n) :
    g.val i j ∈ v.adicCompletionIntegers E ∧ (g⁻¹ : GL (Fin n) (v.adicCompletion E)).val i j ∈ v.adicCompletionIntegers E := by
  obtain ⟨g0, rfl⟩ := hg
  refine ⟨(g0.val i j).2, ?_⟩
  rw [← map_inv]
  exact ((g0⁻¹).val i j).2

theorem glue : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (g : ∀ v : HeightOneSpectrum (𝓞 E), GL (Fin n) (v.adicCompletion E)), (∀ᶠ v in cofinite, g v ∈ GlobalTheory.LFun.KGL v n) → ∃ k : GL (Fin n) (Af E), ∀ v, GeneralLinearGroup.map (pLoc E v) k = g v := by
  intro E _ _ n g hg
  have hent : ∀ i j, ∀ᶠ v in cofinite, (g v).val i j ∈ v.adicCompletionIntegers E ∧
      ((g v)⁻¹ : GL (Fin n) (v.adicCompletion E)).val i j ∈ v.adicCompletionIntegers E :=
    fun i j => hg.mono fun v hv => entry_mem hv i j
  let M : Matrix (Fin n) (Fin n) (Af E) := fun i j => ⟨fun v => (g v).val i j, (hent i j).mono fun v h => h.1⟩
  let N : Matrix (Fin n) (Fin n) (Af E) := fun i j =>
    ⟨fun v => ((g v)⁻¹ : GL (Fin n) (v.adicCompletion E)).val i j, (hent i j).mono fun v h => h.2⟩
  have hM : ∀ v, RingHom.mapMatrix (pLoc E v) M = (g v).val := fun v => rfl
  have hN : ∀ v, RingHom.mapMatrix (pLoc E v) N = ((g v)⁻¹ : GL (Fin n) (v.adicCompletion E)).val := fun v => rfl
  have hMN : M * N = 1 := GlobalTheory.SplitPts.matAf_ext fun v => by
    rw [map_mul, map_one, hM, hN, Units.mul_inv]
  have hNM : N * M = 1 := GlobalTheory.SplitPts.matAf_ext fun v => by
    rw [map_mul, map_one, hM, hN, Units.inv_mul]
  exact ⟨⟨M, N, hMN, hNM⟩, fun v => Units.ext (hM v)⟩

theorem intst : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (v u : HeightOneSpectrum (𝓞 E)) (f : v.adicCompletion E →+* u.adicCompletion E), (∀ x, Valued.v (f x) = Valued.v x) → ∀ g ∈ GlobalTheory.LFun.KGL v n, invT n _ (GeneralLinearGroup.map f g) ∈ GlobalTheory.LFun.KGL u n := by
  intro E _ _ n v u f hf g hg
  obtain ⟨g0, rfl⟩ := hg
  let r : Formalism.UG.Ov E v →+* Formalism.UG.Ov E u := f.restrict _ _ fun x hx => by
    change _ ∈ u.adicCompletionIntegers E
    change x ∈ v.adicCompletionIntegers E at hx
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx ⊢
    rw [hf]
    exact hx
  refine ⟨invT n _ (GeneralLinearGroup.map r g0), ?_⟩
  apply Units.ext
  ext i j
  rfl

theorem ns : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Y : ∀ v : HeightOneSpectrum (𝓞 E), GL (Fin n) (v.adicCompletion E)) (u : HeightOneSpectrum (𝓞 E)), ¬ IsSplitAt u → GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) u) (Y (conjSrc (GlobalTheory.SplitPts.conjE E) u)) = GeneralLinearGroup.map (cj u) (Y u) := by
  intro E _ _ _ n Y u hu
  have key : ∀ (v : HeightOneSpectrum (𝓞 E)) (_ : v = u) (f : v.adicCompletion E →+* u.adicCompletion E), Continuous f →
      (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (IsCMField.complexConj E k)) →
      GeneralLinearGroup.map f (Y v) = GeneralLinearGroup.map (cj u) (Y u) := by
    rintro v rfl f hf hext
    have hex : ∃ s : v.adicCompletion E →+* v.adicCompletion E, Continuous s ∧
        ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := ⟨f, hf, hext⟩
    have hcj : cj v = hex.choose := by unfold cj; rw [dif_pos hex]
    have hfs : (f : v.adicCompletion E → v.adicCompletion E) = hex.choose :=
      (HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf hex.choose_spec.1
        (funext fun k => (hext k).trans (hex.choose_spec.2 k).symm)
    rw [hcj]
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact congrFun hfs ((Y v).val i j)
  have hcu : conjSrc (GlobalTheory.SplitPts.conjE E) u = u := by
    by_contra h
    exact hu ⟨_, h, (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) u _).2
      (Or.inr (GlobalTheory.SplitPts.conjPl_self_conjSrc u))⟩
  exact key _ hcu _ (conjLoc_spec _ u).1 (conjLoc_spec _ u).2.1

theorem twice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Y : ∀ v : HeightOneSpectrum (𝓞 E), GL (Fin n) (v.adicCompletion E)) (u : HeightOneSpectrum (𝓞 E)), GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) u) (GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) (conjSrc (GlobalTheory.SplitPts.conjE E) u)) (Y (conjSrc (GlobalTheory.SplitPts.conjE E) (conjSrc (GlobalTheory.SplitPts.conjE E) u)))) = Y u := by
  intro E _ _ _ n Y u
  have key : ∀ (v : HeightOneSpectrum (𝓞 E)) (_ : v = u) (f : v.adicCompletion E →+* u.adicCompletion E), Continuous f →
      (∀ k : E, f (algebraMap E _ k) = algebraMap E _ k) → GeneralLinearGroup.map f (Y v) = Y u := by
    rintro v rfl f hf hext
    have hfs : (f : v.adicCompletion E → v.adicCompletion E) = id :=
      (HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf continuous_id (funext fun k => hext k)
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact congrFun hfs ((Y v).val i j)
  have h := key _ (GlobalTheory.SplitPts.conjSrc_conjSrc_cm u)
    ((conjLoc (GlobalTheory.SplitPts.conjE E) u).comp (conjLoc (GlobalTheory.SplitPts.conjE E) (conjSrc (GlobalTheory.SplitPts.conjE E) u)))
    ((conjLoc_spec _ u).1.comp (conjLoc_spec _ _).1) fun k => by
      rw [RingHom.comp_apply, (conjLoc_spec _ _).2.1, (conjLoc_spec _ _).2.1]
      exact congrArg _ (IsCMField.complexConj_apply_apply E k)
  rw [← h]
  rfl

end GlobalTheory.BCT.LocGlue

theorem GlobalTheory.BCT.exists_finU_of_loc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ S : Set (Pl E), IsSection S → ∀ y : ∀ w : Pl E, UL n w, (∀ᶠ w in cofinite, y w ∈ KL n w) → ∃ x : finU E n, ∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) = y w := by
  intro E _ _ _ _ n S hS y hy
  set c := GlobalTheory.SplitPts.conjE E with hc
  have hnotS : ∀ v, v ∉ S → conjSrc c v ∈ S := by
    intro v hv
    obtain ⟨s, ⟨hsS, hsv⟩, -⟩ := hS v
    have hne : v ≠ s := fun e => hv (e ▸ hsS)
    have hsp : IsSplitAt s := ⟨v, hne, hsv.symm⟩
    obtain ⟨-, -, hover⟩ := GlobalTheory.SplitPts.over_split hsp
    rcases hover v hsv.symm with h | h
    · exact absurd h hne
    · rw [h, GlobalTheory.SplitPts.conjSrc_conjSrc_cm]; exact hsS
  have hSsplit : ∀ v ∈ S, IsSplitAt v → conjSrc c v ∉ S := by
    intro v hv hsp h
    obtain ⟨hne, hund, -⟩ := GlobalTheory.SplitPts.over_split hsp
    exact hne ((hS v).unique ⟨h, hund⟩ ⟨hv, rfl⟩)
  let z : ∀ v : Pl E, GLw n v := fun v => if v ∈ S then (y v).1 else
    invT n _ (GeneralLinearGroup.map (conjLoc c v) (y (conjSrc c v)).1)
  have hz_in : ∀ v ∈ S, z v = (y v).1 := fun v hv => if_pos hv
  have hz_out : ∀ v, v ∉ S → z v = invT n _ (GeneralLinearGroup.map (conjLoc c v) (y (conjSrc c v)).1) :=
    fun v hv => if_neg hv
  have hint : ∀ᶠ v in cofinite, z v ∈ GlobalTheory.LFun.KGL v n := by
    have h1 : ∀ᶠ v in cofinite, (y v).1 ∈ GlobalTheory.LFun.KGL v n := hy.mono fun v hv => Subgroup.mem_subgroupOf.1 hv
    have h2 := (conjSrc_injective c).tendsto_cofinite.eventually h1
    filter_upwards [h1, h2] with v a1 a2
    by_cases hv : v ∈ S
    · rw [hz_in v hv]; exact a1
    · rw [hz_out v hv]; exact GlobalTheory.BCT.LocGlue.intst E n _ v (conjLoc c v) (conjLoc_spec c v).2.2 _ a2
  obtain ⟨k, hk⟩ := GlobalTheory.BCT.LocGlue.glue E n z hint
  have hk' : ∀ u, ((GeneralLinearGroup.map (pLoc E (conjSrc c u)) k).val.map (conjLoc c u))ᵀ *
      (GeneralLinearGroup.map (pLoc E u) k).val = 1 := by
    intro u
    rw [hk, hk]
    show ((GeneralLinearGroup.map (conjLoc c u) (z (conjSrc c u))).val)ᵀ * (z u).val = 1
    by_cases hu : u ∈ S
    · by_cases hsp : IsSplitAt u
      · rw [hz_out _ (hSsplit u hu hsp), hz_in u hu, GlobalTheory.SplitPts.invT_map,
          GlobalTheory.BCT.LocGlue.twice E n (fun v => (y v).1) u]
        change ((((y u).1)⁻¹ : GLw n u).val)ᵀᵀ * (y u).1.val = 1
        rw [Matrix.transpose_transpose, Units.inv_mul]
      · have hcu : conjSrc c u = u := by
          by_contra h
          exact hsp ⟨_, h, (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
            (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) u _).2
            (Or.inr (GlobalTheory.SplitPts.conjPl_self_conjSrc u))⟩
        rw [hz_in _ (by rw [hcu]; exact hu), hz_in u hu, GlobalTheory.BCT.LocGlue.ns E n (fun v => (y v).1) u hsp]
        have key : ∀ g : GLw n u, g ∈ UL n u → g ∈ UJ (cj u) 1 := by
          intro g hg
          unfold UL at hg
          rwa [if_neg hsp] at hg
        have hUL : (y u).1 ∈ UJ (cj u) 1 := key _ (y u).2
        have h3 : cT (cj u) (y u).1.val * 1 * (y u).1.val = 1 := hUL
        rw [Matrix.mul_one] at h3
        exact h3
    · rw [hz_out u hu, hz_in _ (hnotS u hu)]
      change ((GeneralLinearGroup.map (conjLoc c u) (y (conjSrc c u)).1).val)ᵀ *
        (((GeneralLinearGroup.map (conjLoc c u) (y (conjSrc c u)).1)⁻¹ : GLw n u).val)ᵀ = 1
      rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  let x : finU E n := ⟨⟨finGL E n k, GlobalTheory.SplitPts.finGL_mem_UA k hk'⟩, MonoidHom.mem_ker.2 (pInf_finGL k)⟩
  refine ⟨x, fun w hw => ?_⟩
  show toSub (UL n w) (cLoc w ⟨finGL E n k, GlobalTheory.SplitPts.finGL_mem_UA k hk'⟩) = y w
  rw [GlobalTheory.SplitPts.cLoc_finGL, hk, hz_in w hw]
  unfold toSub
  rw [dif_pos (y w).2]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLCompletionLatticeEqColumns
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.TwLat

theorem exists_GLw_lat_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ L : Submodule K.O B.A, GlobalTheory.UnitLemma.IsLat K.O K.E L → ∃ g : GLw m w, GlobalTheory.TwLat.lat e b g = L := by
  intro E _ _ _ _ w _ K e _ _ _ B m b L hL
  obtain ⟨hfg, hsp⟩ := hL
  haveI : Module.Finite K.O L := Module.Finite.iff_fg.mpr hfg
  haveI : NoZeroSMulDivisors K.O B.A := by
    constructor
    intro c x h
    rw [← algebraMap_smul K.E c x, smul_eq_zero] at h
    rcases h with h | h
    · left; exact (IsFractionRing.injective K.O K.E) (by simpa using h)
    · right; exact h
  haveI : Module.Free K.O L := Module.free_of_finite_type_torsion_free'
  set n := Module.finrank K.O L
  let bL := Module.finBasis K.O L
  let v : Fin n → B.A := fun i => (bL i : B.A)
  have hspanO : Submodule.span K.O (Set.range v) = L := by
    have : Set.range v = L.subtype '' Set.range bL := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, bL.span_eq, Submodule.map_subtype_top]
  have hli : LinearIndependent K.E v := by
    rw [← LinearIndependent.iff_fractionRing K.O K.E]
    exact LinearIndependent.map' bL.linearIndependent L.subtype (by simp)
  have hspE : ⊤ ≤ Submodule.span K.E (Set.range v) := by
    rw [← Submodule.span_span_of_tower K.O K.E (Set.range v), hspanO, hsp]
  let bE := Module.Basis.mk hli hspE
  have hnm : n = m := by
    have h1 := Module.finrank_eq_card_basis bE
    have h2 := Module.finrank_eq_card_basis b
    simp only [Fintype.card_fin] at h1 h2
    omega
  let v' : Fin m → B.A := v ∘ finCongr hnm.symm
  let bE' := bE.reindex (finCongr hnm)
  have hv' : ∀ j, bE' j = v' j := by
    intro j; simp [bE', v', bE, Module.Basis.mk_apply]
  let M : Matrix (Fin m) (Fin m) K.E := b.toMatrix bE'
  have hM : IsUnit M := by
    haveI := b.invertibleToMatrix bE'
    exact isUnit_of_invertible M
  have hMe : IsUnit (M.map e) := hM.map e.mapMatrix
  refine ⟨hMe.unit, ?_⟩
  unfold lat
  rw [← hspanO]
  have hcol : (fun j => ∑ i, e.symm ((hMe.unit : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) • b i) = v' := by
    funext j
    simp only [IsUnit.unit_spec, Matrix.map_apply, RingEquiv.symm_apply_apply, M, Module.Basis.toMatrix_apply]
    rw [b.sum_repr, hv']
  rw [hcol]
  congr 1
  exact EquivLike.range_comp v _

end GlobalTheory.TwLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisConjEigenSystemCongruent
section
open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.ExpFrame.Conj

theorem isEig_map {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (F : Frame l ι N)
    (mu : ι → ℕ → ℕ) (g : PadicAlgCl l ≃+* PadicAlgCl l) (hg : ∀ x, g (F.emb x) = F.emb x)
    (θ : F.I → PadicAlgCl l) (h : F.IsEig mu θ) : F.IsEig mu (fun i => g (θ i)) := by
  obtain ⟨f, hf0, ⟨hΓ, hK⟩, hH⟩ := h
  obtain ⟨Φ, hinj, hsm, hgrp⟩ := GlobalTheory.T.exists_semilinear_action_dualWeylTensor (PadicAlgCl l) ι N mu g
  refine ⟨fun x => Φ (f x), ?_, ⟨fun γ hγ x => by simp only [hΓ γ hγ x], fun κ x => ?_⟩, fun i x => ?_⟩
  · intro h0
    apply hf0
    funext x
    have := congrFun h0 x
    exact hinj (by simpa using this)
  · have hfix : ∀ τ a b, g ((Matrix.GeneralLinearGroup.map F.emb (F.kap κ τ) : Matrix (Fin N) (Fin N) (PadicAlgCl l)) a b) =
        (Matrix.GeneralLinearGroup.map F.emb (F.kap κ τ) : Matrix (Fin N) (Fin N) (PadicAlgCl l)) a b := by
      intro τ a b
      simp [hg]
    rw [← hgrp _ hfix, ← hg (F.chi κ : F.O), ← hsm, hK κ x]
  · have := hH i x
    simp only
    rw [← hg (F.cst i), ← map_sum, ← hsm, this, hsm]

theorem exists_eig_congr : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ), F.Ok → ∀ (θ θ0 : F.I → PadicAlgCl l) (m : Ideal F.T), F.IsEig lam θ → F.Over θ m → F.Over θ0 m → ∃ θ', F.IsEig lam θ' ∧ (∀ i, ‖θ' i‖ ≤ 1) ∧ ∀ i, ‖θ' i - θ0 i‖ < 1 := by
  intro l _ ι _ _ N F lam hOk θ θ0 m hE hθ hθ0
  obtain ⟨_, L, hfin, hrange⟩ := hOk.ring
  have hmemL : ∀ x, F.emb x ∈ L := fun x => by
    have : F.emb x ∈ Set.range F.emb := ⟨x, rfl⟩
    rw [hrange] at this
    exact this.1
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_galois_lift_residue_congruence_padic l L F.I θ θ0 hθ.1 hθ0.1 (by
    intro p hp
    have hmem : p ∈ Set.range (MvPolynomial.map F.emb) := by
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro c hc
      obtain ⟨n, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hc
      rw [hrange]
      exact hp n
    obtain ⟨q, rfl⟩ := hmem
    rw [MvPolynomial.eval_map, MvPolynomial.eval_map, ← hθ.2 q, hθ0.2 q])
  have hn : ∀ x, ‖g x‖ = ‖x‖ := fun x => (spectralNorm_eq_of_equiv (g.restrictScalars ℚ_[l]) x).symm
  refine ⟨fun i => g (θ i), isEig_map F lam g.toRingEquiv (fun x => g.commutes ⟨F.emb x, hmemL x⟩) θ hE,
    fun i => (hn _).trans_le (hθ.1 i), hg⟩

end GlobalTheory.ExpFrame.Conj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalSphericalVectorOfSatakeFamily
section
noncomputable section

open NumberField IsDedekindDomain Matrix Filter

namespace GlobalTheory.JSW.SphVec

open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.LFun

theorem map_mem_twKer {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {K : Subgroup G}
    (S : V →ₗ[ℂ] W) (hS : ∀ h v, S (ρ h v) = σ h (S v)) {v : V} (hv : v ∈ twKer ρ K 1) : S v ∈ twKer σ K 1 := by
  have h : (twKer ρ K 1).map S ≤ twKer σ K 1 := by
    rw [twKer, Submodule.map_span_le]
    rintro _ ⟨n, u, rfl⟩
    exact Submodule.subset_span ⟨n, S u, by simp [hS]⟩
  exact h ⟨v, hv, rfl⟩

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem exists_fixed_mem (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E))
    (hS : GlobalTheory.LGrp.IsSpherical (π.locRep w) (KGL w a)) (U : Submodule ℂ π.V)
    (hU : ∀ g, ∀ v ∈ U, π.locRep w g v ∈ U) {y : π.V} (hy : y ∈ U) (hy0 : y ≠ 0) :
    ∃ x ∈ U, x ≠ 0 ∧ ∀ k ∈ KGL w a, π.locRep w k x = x := by
  have hK : IsCompact ((KGL w a : Subgroup _) : Set (GL (Fin a) (w.adicCompletion E))) :=
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2
  have hsm : IsSmooth (π.locRep w) := π.isSmooth_locRep w
  have hsU : IsSmooth (GlobalTheory.PRep.sub (π.locRep w) U hU) := fun v => by
    convert hsm v.1 using 1
    ext g
    exact Subtype.ext_iff
  by_contra hne
  have hbot : fixed (GlobalTheory.PRep.sub (π.locRep w) U hU) (KGL w a) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    by_contra h0
    exact hne ⟨v.1, v.2, fun h => h0 (Subtype.ext h), fun k hk =>
      congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hv k hk)⟩
  have htop := (GlobalTheory.LocGL.isCompl_fixed_twKer hsU hK).sup_eq_top
  rw [hbot, bot_sup_eq] at htop
  have hall : ∀ g, π.locRep w g y ∈ twKer (π.locRep w) (KGL w a) 1 := fun g =>
    map_mem_twKer (ρ := GlobalTheory.PRep.sub (π.locRep w) U hU) U.subtype (fun _ _ => rfl)
      (v := ⟨_, hU g y hy⟩) (htop ▸ Submodule.mem_top)
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hS
  let Wl : Submodule ℂ π.V := ⨅ g, (twKer (π.locRep w) (KGL w a) 1).comap (π.locRep w g)
  have memWl : ∀ v, v ∈ Wl ↔ ∀ g, π.locRep w g v ∈ twKer (π.locRep w) (KGL w a) 1 := fun v => by
    simp [Wl, Submodule.mem_iInf]
  have stab : GlobalTheory.CuspRep.IsStable (Wl.map π.V.subtype) := by
    rintro o _ ⟨v, hv, rfl⟩
    obtain ⟨g, S, hS, ho⟩ := GlobalTheory.LocFactor.op_eq_locRep_comp π w o
    have hv' := (memWl v).1 hv
    refine ⟨π.op o v, (memWl _).2 fun h => ?_, rfl⟩
    rw [ho, LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul]
    have e := LinearMap.congr_fun (hS (h * g)) v
    simp only [LinearMap.comp_apply] at e
    rw [← e]
    exact map_mem_twKer S (fun h v => LinearMap.congr_fun (hS h) v) (hv' (h * g))
  rcases π.irred _ (Submodule.map_subtype_le _ _) stab with h | h
  · have h1 : (y : Sm E a) ∈ Wl.map π.V.subtype := ⟨y, (memWl y).2 hall, rfl⟩
    rw [h, Submodule.mem_bot] at h1
    exact hy0 (Subtype.ext h1)
  · have h1 : (x : Sm E a) ∈ Wl.map π.V.subtype := by rw [h]; exact x.2
    obtain ⟨x', hx', e⟩ := h1
    obtain rfl : x' = x := Subtype.ext e
    have h2 := (memWl x').1 hx' 1
    rw [map_one, Module.End.one_apply] at h2
    exact hx0 (Submodule.disjoint_def.1 (GlobalTheory.LocGL.isCompl_fixed_twKer hsm hK).disjoint x' hx h2)

theorem locRep_comm (π : CuspSub E a) {v w : HeightOneSpectrum (𝓞 E)} (h : w ≠ v)
    (k : GL (Fin a) (v.adicCompletion E)) (g : GL (Fin a) (w.adicCompletion E)) (x : π.V) :
    π.locRep v k (π.locRep w g x) = π.locRep w g (π.locRep v k x) := by
  simp only [CuspSub.locRep, MonoidHom.comp_apply]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
    LocSph.comm_locGL w _ (pLoc_locGL_of_ne h k)]

theorem exists_fixed_union (π : CuspSub E a) (T : Set (HeightOneSpectrum (𝓞 E))) {y : π.V} (hy0 : y ≠ 0)
    (hy : ∀ v ∈ T, ∀ k ∈ KGL v a, π.locRep v k y = y) (F : Finset (HeightOneSpectrum (𝓞 E)))
    (hF : ∀ w ∈ F, GlobalTheory.LGrp.IsSpherical (π.locRep w) (KGL w a)) :
    ∃ x : π.V, x ≠ 0 ∧ ∀ v, v ∈ T ∨ v ∈ F → ∀ k ∈ KGL v a, π.locRep v k x = x := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨y, hy0, fun v hv => hy v (by simpa using hv)⟩
  | insert w F _ ih =>
    obtain ⟨x, hx0, hx⟩ := ih fun v hv => hF v (Finset.mem_insert_of_mem hv)
    let U : Submodule ℂ π.V := ⨅ v : {v // (v ∈ T ∨ v ∈ F) ∧ w ≠ v}, fixed (π.locRep v.1) (KGL v.1 a)
    have memU : ∀ z, z ∈ U ↔ ∀ v, (v ∈ T ∨ v ∈ F) → w ≠ v → ∀ k ∈ KGL v a, π.locRep v k z = z := fun z => by
      simp only [U, Submodule.mem_iInf, GlobalTheory.LGrp.mem_fixed, Subtype.forall]
      exact ⟨fun h v h1 h2 => h v ⟨h1, h2⟩, fun h v h1 => h v h1.1 h1.2⟩
    obtain ⟨z, hz, hz0, hzw⟩ := exists_fixed_mem π w (hF w (Finset.mem_insert_self _ _)) U
      (fun g z hz => (memU _).2 fun v hv hne k hk => by
        rw [locRep_comm π hne, (memU z).1 hz v hv hne k hk])
      ((memU x).2 fun v hv _ => hx v hv) hx0
    refine ⟨z, hz0, fun v hv => ?_⟩
    by_cases hne : w = v
    · subst hne; exact hzw
    · refine (memU z).1 hz v (hv.imp_right fun h => ?_) hne
      exact (Finset.mem_insert.1 h).resolve_left fun e => hne e.symm

theorem exists_sphVec_of_isSpherical (π : CuspSub E a) (S : Set (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ w ∉ S, GlobalTheory.LGrp.IsSpherical (π.locRep w) (KGL w a)) :
    ∃ φ ∈ π.V, φ ≠ 0 ∧ ∀ w ∉ S, ∀ k ∈ KGL w a, act (.fin (locGL E a w k)) φ = φ := by
  classical
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  have hev := LocSph.eventually_mem ((π.cusp φ hφ).1.level.mem_nhds (by simp))
  rw [Filter.eventually_cofinite] at hev
  obtain ⟨x, hx0, hx⟩ := exists_fixed_union π
    {w | ∀ g : GL (Fin a) (w.adicCompletionIntegers E),
      locGL E a w (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype g) ∈ {k | finRep E a k φ = φ}}
    (y := ⟨φ, hφ⟩) (fun h => h0 (congrArg Subtype.val h))
    (by rintro v hv _ ⟨g, rfl⟩; exact Subtype.ext (hv g))
    (hev.toFinset.filter (· ∉ S)) (fun w hw => hS w (Finset.mem_filter.1 hw).2)
  refine ⟨x.1, x.2, fun h => hx0 (Subtype.ext h), fun w hw k hk => congrArg Subtype.val (hx w ?_ k hk)⟩
  refine (em _).imp_right fun h => Finset.mem_filter.2 ⟨hev.mem_toFinset.2 h, hw⟩

theorem exists_sphVec (π : CuspSub E a) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ w ∉ S, ∃ B, HasSatGL w (π.locRep w) B) :
    ∃ φ ∈ π.V, φ ≠ 0 ∧ ∀ w ∉ S, ∀ k ∈ KGL w a, act (.fin (locGL E a w k)) φ = φ :=
  exists_sphVec_of_isSpherical π S fun w hw => (hS w hw).elim fun _ h => h.1

theorem exists_sphVec_of_hasSat (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ)
    (h : ∀ w ∉ S, HasSatGL w (π.locRep w) (B w)) :
    ∃ φ ∈ π.V, φ ≠ 0 ∧ ∀ w ∉ S, ∀ k ∈ KGL w a, act (.fin (locGL E a w k)) φ = φ :=
  exists_sphVec π S fun w hw => ⟨B w, h w hw⟩

end GlobalTheory.JSW.SphVec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianModelOfOrthonormalBasis
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

noncomputable section

namespace GlobalTheory.KapLat.ModelOfBasis

variable {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K)

theorem herm_sum_left (x z : B.A) {ι : Type} (s : Finset ι) (f : ι → B.A) :
    B.herm x (∑ k ∈ s, f k) z = ∑ k ∈ s, B.herm x (f k) z := by
  unfold GlobalTheory.UnitLemma.InvAlg.herm
  rw [Finset.mul_sum, Finset.sum_mul, map_sum]

theorem herm_sum_right (x y : B.A) {ι : Type} (s : Finset ι) (f : ι → B.A) :
    B.herm x y (∑ k ∈ s, f k) = ∑ k ∈ s, B.herm x y (f k) := by
  unfold GlobalTheory.UnitLemma.InvAlg.herm
  rw [map_sum, Finset.mul_sum, map_sum]

theorem herm_eq_sum {n : ℕ} (x : B.A) (b : Module.Basis (Fin n) K.E B.A)
    (hb : ∀ i j, B.herm x (b i) (b j) = if i = j then 1 else 0) (y z : B.A) :
    B.herm x y z = ∑ k, b.repr y k * K.c (b.repr z k) := by
  conv_lhs => rw [← b.sum_repr y, ← b.sum_repr z]
  rw [herm_sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [herm_sum_right, Finset.sum_eq_single k]
  · rw [GlobalTheory.UnitLemma.Basic.herm_smul_left, GlobalTheory.UnitLemma.Basic.herm_smul_right, hb, if_pos rfl]; ring
  · intro l _ hl
    rw [GlobalTheory.UnitLemma.Basic.herm_smul_left, GlobalTheory.UnitLemma.Basic.herm_smul_right, hb, if_neg (Ne.symm hl)]; ring
  · intro h; exact absurd (Finset.mem_univ k) h

end GlobalTheory.KapLat.ModelOfBasis

open GlobalTheory.KapLat.ModelOfBasis in
theorem GlobalTheory.KapLat.exists_model_of_orthonormal_basis :
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w →
    ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e →
    ∀ (n : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A), u * B.σ u = 1 →
    ∀ b : Module.Basis (Fin n) K.E B.A, (∀ i j, B.herm x (b i) (b j) = if i = j then 1 else 0) →
    ∃ γ : GLw n w, γ ∈ UL n w ∧ IsModel w e B u x γ := by
  intro E _ _ _ w hw K e hbr n B u x hu b hb
  let ψ : B.A ≃+ (Fin n → w.adicCompletion E) :=
    b.equivFun.toAddEquiv.trans (AddEquiv.piCongrRight fun _ => e.toAddEquiv)
  have hψ : ∀ y k, ψ y k = e (b.repr y k) := fun y k => rfl
  have hstd : ∀ y z, stdH w (ψ y) (ψ z) = e (B.herm x y z) := by
    intro y z
    rw [herm_eq_sum B x b hb, map_sum]
    unfold stdH
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hψ, hψ, map_mul, hbr.1]
  let M : Matrix (Fin n) (Fin n) (w.adicCompletion E) := Matrix.of fun k i => e (b.repr (u * b i) k)
  have hM : ∀ y, ψ (u * y) = M *ᵥ ψ y := by
    intro y
    funext k
    have hy : u * y = ∑ i, b.repr y i • (u * b i) := by
      conv_lhs => rw [← b.sum_repr y]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => mul_smul_comm _ _ _
    rw [hψ, hy, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, map_sum]
    simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply, hψ, map_smul, Finsupp.smul_apply, smul_eq_mul,
      map_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hunit : cT (cj w) M * M = 1 := by
    ext i j
    have h := hstd (u * b j) (u * b i)
    rw [← GlobalTheory.UnitLemma.Basic.herm_norm, hu, mul_one, hb] at h
    simp only [stdH, hψ] at h
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, M, Matrix.of_apply]
    rw [Finset.sum_congr rfl fun k _ => mul_comm _ _, h]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg (Ne.symm hij), if_neg hij, map_zero]
  have hunit' : M * cT (cj w) M = 1 := mul_eq_one_comm.mp hunit
  let γ : GLw n w := ⟨M, cT (cj w) M, hunit', hunit⟩
  refine ⟨γ, ?_, ψ, ?_, hM, hstd⟩
  · unfold UL
    rw [if_neg hw]
    show cT (cj w) M * 1 * M = 1
    rw [Matrix.mul_one, hunit]
  · intro c y
    funext k
    rw [hψ, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Pi.smul_apply, hψ, smul_eq_mul]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogCutoffCoordinateHyperplanesPoincareBounStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_logCutoff_coordinateHyperplanes_poincareBound : ∀ {n : ℕ} (S : Finset (Fin n)), ∃ (C : ℝ) (χ : ℕ → V n → ℝ), (∀ k, ContDiff ℝ ∞ (χ k)) ∧ (∀ k v, 0 ≤ χ k v ∧ χ k v ≤ 1) ∧ (∀ k v, (∃ a ∈ S, v a = 0) → χ k =ᶠ[𝓝 v] fun _ => 0) ∧ (∀ v : V n, (∀ a ∈ S, v a ≠ 0) → ∀ᶠ k in atTop, χ k =ᶠ[𝓝 v] fun _ => 1) ∧ ∀ k v b, ‖dbar (fun x => (χ k x : ℂ)) v (coordVec b)‖ * poinWt S v b ≤ C := by
  first | exact @GlobalTheory.GoodTop.exists_logCutoff_hyperplanes | exact GlobalTheory.GoodTop.exists_logCutoff_hyperplanes | (intros; apply GlobalTheory.GoodTop.exists_logCutoff_hyperplanes <;> assumption)
end

