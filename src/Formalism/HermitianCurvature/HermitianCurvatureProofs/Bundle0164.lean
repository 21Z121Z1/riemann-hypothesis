import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0159
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0160
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0084

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPPCommPf
section
open Matrix Finset Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace PCommPf

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq]

theorem isOpen_slice {Dc : (Fin r → ℂ) → Set (Q.Mx k r)}
    (ho : IsOpen {x : (Fin r → ℂ) × Q.Mx k r | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1}) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    IsOpen (Dc c) := by
  have h := ho.preimage (continuous_const.prodMk continuous_id : Continuous (fun g : Q.Mx k r => (c, g)))
  convert h using 1
  ext g
  exact ⟨fun hg => ⟨hc, hg⟩, fun hg => hg.2⟩

theorem tL_crd_comm (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (Dc : (Fin r → ℂ) → Set (Q.Mx k r))
    (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) (ho : IsOpen {x : (Fin r → ℂ) × Q.Mx k r | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1})
    (hΨ : Q.SmoothFam k r i {x | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1} Ψ) (l : Fin r) (Y : ℂ) (a b : Fin 2)
    {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r i) (hgD : g ∈ Dc c) :
    Q.crd (pOp l) (Q.QL k r z z' i Y a b Ψ) c g = Q.QL k r z z' i Y a b (Q.crd (pOp l) Ψ) c g ∧
    Q.crd (pbOp l) (Q.QL k r z z' i Y a b Ψ) c g = Q.QL k r z z' i Y a b (Q.crd (pbOp l) Ψ) c g := by
  have hO : IsOpen (Dc c) := isOpen_slice ho hc
  have hgG : g ∈ Q.Glev k r i ∩ Dc c := ⟨hg, hgD⟩
  have hx : ((c, g) : Qx8.XX k r) ∈ Qx8.UU Dc := ⟨hc, hgD⟩
  have hcd := Qx8.cd_tL (E := Wq →L[ℂ] Wp) (i := i) (U₀ := Qx8.UU Dc) ho z z' Y a b
  have hder : ∀ s s₂ : ℂ,
      s • ((1 / 2 : ℂ) • (Qx8.dv (Pi.single l 1) (fun c' => Q.tL k r z z' i Y a b (Ψ c')) c g +
        s₂ • Qx8.dv (Pi.single l Complex.I) (fun c' => Q.tL k r z z' i Y a b (Ψ c')) c g)) =
      Q.tL k r z z' i Y a b (fun g' => s • ((1 / 2 : ℂ) • (Qx8.dv (Pi.single l 1) Ψ c g' +
        s₂ • Qx8.dv (Pi.single l Complex.I) Ψ c g'))) g := by
    intro s s₂
    rw [hcd.comm _ Ψ hΨ (c, g) hx hg, hcd.comm _ Ψ hΨ (c, g) hx hg, smul_smul]
    have := Qx8.tl_comb (z := z) (z' := z') (i := i) Formalism.FourierDecayAlt.P.transfer_linear_local hO Y a b (s * (1 / 2)) s₂
      (Qx8.sf_slice (Qx8.sf_dv (Pi.single l 1) hΨ) hc)
      (Qx8.sf_slice (Qx8.sf_dv (Pi.single l Complex.I) hΨ) hc) hgG
    rw [← this]
    simp only [smul_smul]
  refine ⟨?_, ?_⟩
  · show pOp l (fun c' => Q.tL k r z z' i Y a b (Ψ c') g) c =
      Q.tL k r z z' i Y a b (fun g' => pOp l (fun c' => Ψ c' g') c) g
    have h := hder (c l) (-Complex.I)
    simp only [pOp, if_pos hc, wirt]
    simp only [Qx8.dv, neg_smul, ← sub_eq_add_neg] at h
    exact h
  · show pbOp l (fun c' => Q.tL k r z z' i Y a b (Ψ c') g) c =
      Q.tL k r z z' i Y a b (fun g' => pbOp l (fun c' => Ψ c' g') c) g
    have h := hder (star (c l)) Complex.I
    simp only [pbOp, if_pos hc, wirtBar]
    simp only [Qx8.dv] at h
    exact h

end PCommPf

theorem residue_projection_commutation : JDRPComm := by
  intro Wp Wq _ _ _ _ k r z z' π π' Dc Ψ _ _ ho hΨ l Y a b c hc g hg hgD
  exact (PCommPf.tL_crd_comm z z' (Fin.last r) Dc Ψ ho hΨ.1 l Y a b hc hg hgD).1

theorem crd_pbOp_QL_last_comm :
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (Dc : (Fin r → ℂ) → Set (Q.Mx k r)) (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)), inWb k r z → inWb k r z' →
    IsOpen {x : (Fin r → ℂ) × Q.Mx k r | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1} →
    Q.FamFF k r z z' π π' (Fin.last r) Dc Ψ →
    ∀ (l : Fin r) (Y : ℂ) (a b : Fin 2), ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), g ∈ Dc c →
      Q.crd (Formalism.QuantumDeterminants.pbOp l) (Q.QL k r z z' (Fin.last r) Y a b Ψ) c g =
        Q.QL k r z z' (Fin.last r) Y a b (Q.crd (Formalism.QuantumDeterminants.pbOp l) Ψ) c g := by
  intro Wp Wq _ _ _ _ k r z z' π π' Dc Ψ _ _ ho hΨ l Y a b c hc g hg hgD
  exact (PCommPf.tL_crd_comm z z' (Fin.last r) Dc Ψ ho hΨ.1 l Y a b hc hg hgD).2

end Formalism.FourierDecayAlt.P.CutMP

end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRInvDefs
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open Matrix

noncomputable section

def alP (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (k + 1)) : ℂ :=
  ((-1 : ℂ) ^ (i : ℕ)) * herm (Hpk k r) (bvec (wI k r i)) z'

def beM (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (t : Fin (k + 1)) : ℂ :=
  ((-1 : ℂ) ^ (t : ℕ)) * z' (wI k r t)

def RInvAlphaP : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (w m : B.Mat k r), inWb k r z' → w ∈ UWset k r z' → m ∈ Nset k r →
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (X : (Fin (r + k) → Fin (2 * r + k + 1)) → M),
      ∑ c ∈ jSetR k r, (∑ i : Fin (k + 1), alP k r z' i * ((m * w)⁻¹.submatrix c (rowsR k r i)).det) • X c =
        ((m * w)⁻¹).det • ∑ i : Fin (k + 1), alP k r z' i • X (rowsR k r i)

def RInvBetaP : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (g S : B.Mat k r), g ∈ B.GV k r → S ∈ B.GV k r →
    ∀ d : Fin (r + k) → Fin (2 * r + k + 1),
      ∑ J ∈ jSetR k r, beJ k r z g J * (S.submatrix J d).det = S.det * beJ k r z (g * S) d

def RInvBetaLeftP : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (h m g : B.Mat k r), inWb k r z → h ∈ UWset k r z → m ∈ Nset k r →
    g ∈ B.GV k r → ∀ J : Fin (r + k) → Fin (2 * r + k + 1), beJ k r z (h⁻¹ * m⁻¹ * g) J = beJ k r z g J

def RInvAlphaM : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (g S : B.Mat k r), g ∈ B.GV k r → S ∈ B.GV k r →
    ∀ c : Fin (r + k) → Fin (2 * r + k + 1),
      ∑ J ∈ jSetR k r, alJ k r z g J * ((S⁻¹).submatrix c J).det = (S⁻¹).det * alJ k r z (g * S) c

def RInvAlphaLeftM : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (h m g : B.Mat k r), inWb k r z → h ∈ UWset k r z → m ∈ Nset k r →
    g ∈ B.GV k r → ∀ J : Fin (r + k) → Fin (2 * r + k + 1), alJ k r z (h⁻¹ * m⁻¹ * g) J = alJ k r z g J

def RInvBetaM : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (w m : B.Mat k r), inWb k r z' → w ∈ UWset k r z' → m ∈ Nset k r →
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (X : (Fin (r + k) → Fin (2 * r + k + 1)) → M),
      ∑ d ∈ jSetR k r, (∑ t : Fin (k + 1), beM k r z' t * ((m * w).submatrix (colsV k r t) d).det) • X d =
        (m * w).det • ∑ t : Fin (k + 1), beM k r z' t • X (colsV k r t)

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHBTl
section
namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

theorem boundary_torus_adjoin : CutSH.BTlAdjoin := by
  intro Wp Wq _ _ _ _ _ _ k r z z' π π' X L hX S _ _ l w a b
  set Qa : Subalgebra ℂ (Module.End ℂ (RadSp k r z z' π π')) := Algebra.adjoin ℂ (Set.range (X.op l)) with hQa
  let good : Pr (RadSp k r z z' π π') → Prop := fun x => x.1 ∈ Qa ∧ x.2.unop ∈ Qa
  have hop : ∀ i, X.op l i ∈ Qa := fun i => Algebra.subset_adjoin ⟨i, rfl⟩
  have gmul : ∀ x y, good x → good y → good (x * y) := fun x y hx hy =>
    ⟨Subalgebra.mul_mem _ hx.1 hy.1, Subalgebra.mul_mem _ hy.2 hx.2⟩
  have gadd : ∀ x y, good x → good y → good (x + y) := fun x y hx hy =>
    ⟨Subalgebra.add_mem _ hx.1 hy.1, Subalgebra.add_mem _ hx.2 hy.2⟩
  have gneg : ∀ x, good x → good (-x) := fun x hx => ⟨Subalgebra.neg_mem _ hx.1, Subalgebra.neg_mem _ hx.2⟩
  have gzero : good 0 := ⟨Subalgebra.zero_mem _, Subalgebra.zero_mem _⟩
  have gone : good 1 := ⟨Subalgebra.one_mem _, Subalgebra.one_mem _⟩
  have gstar : ∀ x, good x → good (star x) := fun x hx => ⟨hx.2, hx.1⟩
  have galg : ∀ c : ℂ, good (algebraMap ℂ (Pr (RadSp k r z z' π π')) c) := fun c =>
    ⟨Subalgebra.algebraMap_mem _ c, Subalgebra.algebraMap_mem _ (starRingEnd ℂ c)⟩
  have gp : good (L.p l) := by
    rw [hX.1 l]
    exact ⟨hop 0, Subalgebra.neg_mem _ (hop 3)⟩
  have gc : good (L.c l) := by
    rw [hX.2.2.1 l]
    exact ⟨hop 1, hop 4⟩
  have gci : good (L.ci l) := by
    rw [hX.2.2.2.1 l]
    exact ⟨hop 2, hop 5⟩
  have hTs : ∀ (Y : ℂ) (i j : Fin 2), good ((Wd.Ts (site L l) Y) i j) := by
    intro Y i j
    fin_cases i <;> fin_cases j <;>
      simp only [Wd.Ts, site, Formalism.YangianSpanCharacter.T.Tm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
        Fin.zero_eta, Fin.mk_one]
    · exact gadd _ _ (galg Y) gp
    · exact gneg _ gc
    · exact gci
    · exact gzero
  have hmulA : ∀ M N : Wd.SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π')), (∀ a b, good (M a b)) → (∀ a b, good (N a b)) →
      ∀ a b, good ((M * N) a b) := by
    intro M N hM hN a b
    rw [Matrix.mul_apply]
    refine Finset.sum_induction _ good (fun x y hx hy => gadd x y hx hy) gzero (fun c _ => ?_)
    exact gmul _ _ (hM a c) (hN c b)
  have hsumA : ∀ (ι : Type) (t : Finset ι) (f : ι → Wd.SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))),
      (∀ i, ∀ a b, good (f i a b)) → ∀ a b, good ((∑ i ∈ t, f i) a b) := by
    intro ι t f hf a b
    rw [Matrix.sum_apply]
    exact Finset.sum_induction _ good (fun x y hx hy => gadd x y hx hy) gzero (fun i _ => hf i a b)
  have heU : ∀ (x : S) (i j : Fin 2), ∀ a b, good ((Wd.eU (A := Pr (RadSp k r z z' π π')) x i j : Wd.SlopeTestRemainingChoices S _) a b) := by
    intro x i j a b
    unfold Wd.eU
    simp only [Matrix.of_apply]
    split_ifs
    · exact gone
    · exact gzero
  have hio : ∀ y, good y → ∀ a b, good ((Wd.io (S := S) y) a b) := by
    intro y hy a b
    unfold Wd.io
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · exact hy
    · exact gzero
  have hvlet : ∀ lt : Wd.Letter ℂ S, ∀ a b, good ((Wd.vlet (site L l) lt) a b) := by
    intro lt
    unfold Wd.vlet Wd.ins
    refine hsumA _ _ _ (fun i => ?_)
    refine hsumA _ _ _ (fun j => ?_)
    refine hmulA _ _ (heU _ i j) ?_
    intro a b
    unfold Wd.lift0
    rw [Matrix.map_apply]
    refine hio _ ?_ a b
    split_ifs
    · exact hTs _ i j
    · rw [Matrix.map_apply]
      exact gstar _ (hTs _ i j)
  have hbT : ∀ w' : List (Wd.Letter ℂ S), ∀ a b, good ((Wd.bT (site L l) w') a b) := by
    intro w'
    induction w' with
    | nil =>
      intro a b
      simp only [Wd.bT]
      rw [Matrix.one_apply]
      split_ifs
      · exact gone
      · exact gzero
    | cons lt w' ih =>
      intro a b
      simp only [Wd.bT]
      exact hmulA _ _ (hvlet lt) ih a b
  exact (hbT w a b).1

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHFamAlg
section
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem family_algebraic : FamAlg := by
  intro Wp Wq _ _ _ _ _ _ P T j G G' hG hG' m hm
  obtain ⟨hG1, hG2⟩ := hG
  obtain ⟨hG1', hG2'⟩ := hG'
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro t₀ ht₀ γ₀ hγ₀
    obtain ⟨U, f, hU, hmem, hf, hfe⟩ := hG1 t₀ ht₀ γ₀ hγ₀
    obtain ⟨U', f', hU', hmem', hf', hfe'⟩ := hG1' t₀ ht₀ γ₀ hγ₀
    refine ⟨U ∩ U', fun p => f p + f' p, hU.inter hU', ⟨hmem, hmem'⟩,
      (hf.mono Set.inter_subset_left).add (hf'.mono Set.inter_subset_right), ?_⟩
    intro p hp hpG
    simp only [hfe p hp.1 hpG, hfe' p hp.2 hpG]
  · intro K hK hK0
    obtain ⟨C, hC, ε, hε, hCε⟩ := hG2 K hK hK0
    obtain ⟨C', hC', ε', hε', hCε'⟩ := hG2' K hK hK0
    refine ⟨C ∪ C', hC.union hC', min ε ε', lt_min hε hε', ?_⟩
    intro t ht γ hne
    by_cases h0 : G t γ = 0
    · have h1 : G' t γ ≠ 0 := by
        intro h1; apply hne; simp [h0, h1]
      obtain ⟨hγ, hb⟩ := hCε' t ht γ h1
      exact ⟨Or.inr hγ, fun hg => (min_le_right _ _).trans (hb hg)⟩
    · obtain ⟨hγ, hb⟩ := hCε t ht γ h0
      exact ⟨Or.inl hγ, fun hg => (min_le_left _ _).trans (hb hg)⟩
  · intro t₀ ht₀ γ₀ hγ₀
    obtain ⟨U, f, hU, hmem, hf, hfe⟩ := hG1 t₀ ht₀ γ₀ hγ₀
    have hO : IsOpen {p : ℂ × B.Mat P.k (P.r - (j + 1)) | p.1 ≠ 0} :=
      isOpen_ne_fun continuous_fst continuous_const
    refine ⟨U ∩ {p | p.1 ≠ 0}, fun p => m p.1 • f p, hU.inter hO, ⟨hmem, ht₀⟩, ?_, ?_⟩
    · have hm' : ContDiffOn ℝ ∞ (fun p : ℂ × B.Mat P.k (P.r - (j + 1)) => m p.1) (U ∩ {p | p.1 ≠ 0}) :=
        hm.comp contDiffOn_fst (fun p hp => hp.2)
      exact hm'.smul (hf.mono Set.inter_subset_left)
    · intro p hp hpG
      simp only [hfe p hp.1 hpG]
  · intro K hK hK0
    obtain ⟨C, hC, ε, hε, hCε⟩ := hG2 K hK hK0
    exact ⟨C, hC, ε, hε, fun t ht γ hne => hCε t ht γ (right_ne_zero_of_smul hne)⟩

end Formalism.FourierDecayAlt.P.CutSH
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHFamDeriv
section
open MeasureTheory
open scoped ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH Formalism.FourierDecayAlt.P.CutSH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem family_derivative : CutSH.FamDeriv := by
  intro Wp Wq _ _ _ _ _ _ P T j G hG v
  obtain ⟨hloc, hsupp⟩ := hG
  refine ⟨?_, ?_⟩
  · intro t₀ ht₀ γ₀ hγ₀
    obtain ⟨U, f, hU, hmem, hf, hGf⟩ := hloc t₀ ht₀ γ₀ hγ₀
    refine ⟨U, fun p => fderiv ℝ f p ((v, 0) : ℂ × B.Mat P.k (P.r - (j + 1))), hU, hmem, ?_, ?_⟩
    · exact (hf.fderiv_of_isOpen (m := ∞) hU (by simp)).clm_apply contDiffOn_const
    · rintro ⟨t, γ⟩ hp hγ
      simp only [famP, Set.indicator_of_mem hγ]
      have hev : (fun u : ℂ => G u γ) =ᶠ[𝓝 t] fun u => f (u, γ) := by
        have hc : Continuous fun u : ℂ => (u, γ) := continuous_id.prodMk continuous_const
        have : ∀ᶠ u in 𝓝 t, (u, γ) ∈ U := hc.continuousAt.preimage_mem_nhds (hU.mem_nhds hp)
        filter_upwards [this] with u hu
        exact hGf (u, γ) hu hγ
      rw [hev.fderiv_eq]
      have hfd : DifferentiableAt ℝ f (t, γ) :=
        (hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hp)
      have hin := hasFDerivAt_prodMk_left (𝕜 := ℝ) t γ
      rw [show (fun u : ℂ => f (u, γ)) = f ∘ fun u => (u, γ) from rfl, (hfd.hasFDerivAt.comp t hin).fderiv]
      rfl
  · intro K hK hK0
    obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open (isOpen_compl_singleton (x := (0 : ℂ)))
      (fun t ht => by simpa using hK0 t ht)
    obtain ⟨C, hC, ε, hε, hCε⟩ := hsupp (Metric.cthickening δ K) hK.cthickening
      (fun t ht => by simpa using hsub ht)
    refine ⟨C, hC, ε, hε, fun t ht γ hne => ?_⟩
    have hγ : γ ∈ B.GV P.k (P.r - (j + 1)) := by
      by_contra h
      exact hne (by simp [famP, Set.indicator_of_notMem h])
    have hd : fderiv ℝ (fun u : ℂ => G u γ) t v ≠ 0 := by
      simpa [famP, Set.indicator_of_mem hγ] using hne
    have hex : ∃ u ∈ Metric.ball t δ, G u γ ≠ 0 := by
      by_contra hno
      push Not at hno
      have hev : (fun u : ℂ => G u γ) =ᶠ[𝓝 t] fun _ => 0 := by
        filter_upwards [Metric.ball_mem_nhds t hδ] with u hu using hno u hu
      exact hd (by rw [hev.fderiv_eq]; simp)
    obtain ⟨u, hu, hGu⟩ := hex
    have huK : u ∈ Metric.cthickening δ K :=
      Metric.mem_cthickening_of_dist_le u t δ K ht (le_of_lt (Metric.mem_ball.mp hu))
    obtain ⟨hγC, hε'⟩ := hCε u huK γ hGu
    exact ⟨hγC, fun _ => hε' hγ⟩

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHFamJFOK
section
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem family_orbital_valid : FamJFOK := by
  intro Wp Wq _ _ _ _ _ _ P T j G hG t ht
  obtain ⟨hsm, hcpt⟩ := hG
  obtain ⟨C, hC, ε, hε, hCε⟩ := hcpt {t} isCompact_singleton (by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    exact ht)
  have hzero : ∀ γ, γ ∉ C → G t γ = 0 := by
    intro γ hγ
    by_contra h
    exact hγ (hCε t rfl γ h).1
  have hCk : B.CkOn ⊤ (B.GV P.k (P.r - (j + 1))) (G t) := by
    intro γ₀ hγ₀
    obtain ⟨U, f, hU, hmem, hf, hfe⟩ := hsm t ht γ₀ hγ₀
    refine ⟨(fun γ => (t, γ)) ⁻¹' U, fun γ => f (t, γ), ?_, hmem, ?_, ?_⟩
    · exact hU.preimage (continuous_const.prodMk continuous_id)
    · have hd : ContDiff ℝ ∞ (fun γ : B.Mat P.k (P.r - (j + 1)) => (t, γ)) :=
        contDiff_const.prodMk contDiff_id
      exact hf.comp hd.contDiffOn (fun γ hγ => hγ)
    · intro γ hγ hγV
      exact hfe (t, γ) hγ hγV
  refine ⟨⟨?_, ε, hε, ?_⟩, ?_⟩
  · exact JFxG.cptInCC_G hCk hC (fun g _ hg => hzero g hg)
  · intro g hg hne
    exact (hCε t rfl g hne).2 hg
  · refine HasCompactSupport.intro hC ?_
    exact hzero

end Formalism.FourierDecayAlt.P.CutSH
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHSFG
section
open MeasureTheory
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH.SFG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def pt {k ρ m : ℕ} (e : ρ + 1 = m) (t : ℂ) (γ : B.Mat k ρ) (xx : U.RC k 1 ρ × U.RC k 1 ρ) : B.Mat k m :=
  (rn1 e xx.1)⁻¹ * mc e t γ * rn1 e xx.2

def GfStep : Prop :=
  ∀ (k ρ m : ℕ) (e : ρ + 1 = m) (z z' : Fin (2 * ρ + k + 1) → ℂ), inWb k ρ z → inWb k ρ z' →
    ∀ (t : ℂ), t ≠ 0 → ∀ (γ : B.Mat k ρ)
    (xx : U.RC k 1 ρ × U.RC k 1 ρ),
    Gf k m (D.castV e (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z)))
        (D.castV e (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z'))) (pt e t γ xx) =
      ‖t‖ ^ 2 * Gf k ρ z z' γ

def RadProper : Prop :=
  ∀ (k ρ m : ℕ) (e : ρ + 1 = m) (δ R : ℝ), 0 < δ →
    ∃ (Kx : Set (U.RC k 1 ρ × U.RC k 1 ρ)) (C : Set (B.Mat k ρ)), IsCompact Kx ∧ IsCompact C ∧
      ∀ (t : ℂ) (γ : B.Mat k ρ) (xx : U.RC k 1 ρ × U.RC k 1 ρ), δ ≤ ‖t‖ → B.gN (pt e t γ xx) ≤ R →
        xx ∈ Kx ∧ γ ∈ C

def ParamSmooth : Prop :=
  ∀ (Pm X W : Type) [NormedAddCommGroup Pm] [NormedSpace ℝ Pm] [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (h : Pm → X → W) (s : Set Pm) (K : Set X),
    IsOpen s → IsCompact K → (∀ p ∈ s, ∀ x, x ∉ K → h p x = 0) →
    ContDiffOn ℝ ∞ (fun q : Pm × X => h q.1 q.2) (s ×ˢ Set.univ) →
    ContDiffOn ℝ ∞ (fun p => ∫ x, h p x ∂μ) s

def PtSmooth : Prop :=
  ∀ (k ρ m : ℕ) (e : ρ + 1 = m),
    ContDiffOn ℝ ∞ (fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) => pt e q.1.1 q.1.2 q.2)
      ({p : ℂ × B.Mat k ρ | p.1 ≠ 0} ×ˢ Set.univ) ∧
    ∀ z : Fin (2 * m + k + 1) → ℂ, ContDiff ℝ ∞ (fun x : U.RC k 1 ρ => psi k m z cStd (rn1 e x))

def PtGV : Prop :=
  ∀ (k ρ m : ℕ) (e : ρ + 1 = m) (t : ℂ), t ≠ 0 → ∀ γ ∈ B.GV k ρ, ∀ xx : U.RC k 1 ρ × U.RC k 1 ρ,
    pt e t γ xx ∈ B.GV k m

def CkExt : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F : B.Mat k r → E),
    B.CkOn (⊤ : ℕ∞) (B.GV k r) F → HasCompactSupport F →
    ∃ Ft : B.Mat k r → E, ContDiff ℝ ∞ Ft ∧ HasCompactSupport Ft ∧ ∀ g ∈ B.GV k r, Ft g = F g

end Formalism.FourierDecayAlt.P.CutSH.SFG
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHUUiw
section
namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

private theorem matrix_mul_entries_mem_bot_subalgebra {A ι : Type} [Ring A] [Algebra ℂ A] [Fintype ι] {M N : Matrix ι ι A}
    (hM : ∀ x y, M x y ∈ (⊥ : Subalgebra ℂ A)) (hN : ∀ x y, N x y ∈ (⊥ : Subalgebra ℂ A)) :
    ∀ x y, (M * N) x y ∈ (⊥ : Subalgebra ℂ A) := by
  intro x y
  rw [Matrix.mul_apply]
  exact Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ (hM x k) (hN k y)

private theorem ite_zero_mem_bot_subalgebra {A : Type} [Ring A] [Algebra ℂ A] (p : Prop) [Decidable p] (u : A)
    (hu : u ∈ (⊥ : Subalgebra ℂ A)) : (if p then u else 0) ∈ (⊥ : Subalgebra ℂ A) := by
  split_ifs
  · exact hu
  · exact Subalgebra.zero_mem _

theorem unipotent_scalar_identity : CutSH.UUiwScalar := by
  intro A _ _ _ S _ _ s w
  induction w with
  | nil =>
    intro a b
    show (1 : Wd.SlopeTestRemainingChoices S A) a b ∈ _
    rw [Matrix.one_apply]
    exact ite_zero_mem_bot_subalgebra _ _ (Subalgebra.one_mem _)
  | cons l w ih =>
    intro a b
    show ((Wd.ins l.intersection_update_fsHerm_neg_one (Wd.lift0 (YangianSpanCharacter.T.Uinv (if l.plus = true then s else star s))) : Wd.SlopeTestRemainingChoices S A) *
      (Wd.UUiw s w : Wd.SlopeTestRemainingChoices S A)) a b ∈ _
    refine matrix_mul_entries_mem_bot_subalgebra ?_ ih a b
    intro x y
    simp only [Wd.ins, Matrix.sum_apply]
    refine Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ => ?_
    refine matrix_mul_entries_mem_bot_subalgebra ?_ ?_ x y
    · intro u v
      simp only [Wd.eU, Matrix.of_apply]
      exact ite_zero_mem_bot_subalgebra _ _ (Subalgebra.one_mem _)
    · intro u v
      have hU : YangianSpanCharacter.T.Uinv (A := A) (if l.plus = true then s else star s) i j ∈ (⊥ : Subalgebra ℂ A) := by
        fin_cases i <;> fin_cases j <;>
          simp [YangianSpanCharacter.T.Uinv, Subalgebra.one_mem, Subalgebra.zero_mem, Subalgebra.algebraMap_mem]
      simp only [Wd.lift0, Matrix.map_apply, Wd.io, Matrix.scalar_apply, Matrix.diagonal_apply]
      exact ite_zero_mem_bot_subalgebra _ _ hU

end Formalism.FourierDecayAlt.P
end

