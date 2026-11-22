import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0149
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0147
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0109
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0111
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0110
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemClosureIff
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0004
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousBdGen
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0126
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0142
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0092
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0096
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0148
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeightsranchOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0096
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLevelPrimePointModelRealisation
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TilLatticesOfLevel

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EvaluationMapTrueChainFormsToFormsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evaluationMap_trueChain_forms_to_forms : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι), (∀ φ ∈ ((I.tw l l0 Z).fm u a).Fi B.R.m, GlobalTheory.PerQ.PtT (I.rec7 l Z) u a φ ∈ ((I.tw l l0 Z).fm u a).ptC) ∧ ((I.rec7 l Z).fm u).SgInterlace := by
  first | exact @GlobalTheory.PerQ.ptT_forms_built | exact GlobalTheory.PerQ.ptT_forms_built | (intros; apply GlobalTheory.PerQ.ptT_forms_built <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIntegralHyperplaneFormOfLocalCoordsIntegra
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerQ.Co.PtInt

theorem natW_sgT {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι) (τ : B.fields.Tau) :
    ((I.perIn u a).sgT τ).natW = ((I.perIn u a).sg τ).natW := by
  funext i
  simp only [DomWeight.natW, PerIn.sgT, Col2.shW, DomWeight.detShift]
  split_ifs with h
  · congr 1
    ring
  · exact absurd i.2 (by omega)

theorem invTrK_bc {E K ι : Type} [Field E] [Field K] (emb : ι → E →+* K) (σ : K →+* ℂ) {n : ℕ} (γ : GL (Fin n) E) :
    (fun τ => Formalism.UG.bc σ (invTrK (embGL emb γ) τ)) = invTrK (embGL (embAt σ emb) γ) := by
  funext τ
  ext a b
  have h1 := GlobalTheory.LvT.BuiltChain.invTrK_embGL_apply emb γ τ a b
  have h2 := GlobalTheory.LvT.BuiltChain.invTrK_embGL_apply (embAt σ emb) γ τ a b
  rw [h2]
  show σ (((invTrK (embGL emb γ) τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b) = _
  rw [h1]
  rfl

end GlobalTheory.PerQ.Co.PtInt

theorem GlobalTheory.PerQ.Co.PtInt.exists_mem_SP_of_coP_mem : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι) (w : B.places.Pl), ∀ z ∈ ((I.tw l l0 Z).fm u a).ptC, (∀ c, GlobalTheory.PerQ.Co.coP I u a w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan (I.rec7 l Z) w ((I.rec7 l Z).fm u).sg) → ∃ y ∈ ((I.tw l l0 Z).fm u a).SP w, ((I.tw l l0 Z).fm u a).ptEmb y = z := by
  intro B X I hI l Z l0 u a w z hz hco
  have hOk : (I.perIn u a).S'.Ok := (l.per u a).step
  have hz' : z ∈ (I.perIn u a).S'.Fi B.fields.emb B.embLL (I.perIn u a).sgT := hz
  have key : ∀ c : (I.perIn u a).S'.Cl, ∃ v : Formalism.L2.DIV.VV B.fields.K (I.perIn u a).sgT,
      z c = evV B.fields.emb (1 : Matrix _ _ B.fields.E) (I.perIn u a).sgT B.embLL v ∧
      v ∈ locW B.places w (delAtr B.fields.emb (I.perIn u a).sgT ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c))) := by
    intro c
    obtain ⟨P, hP, hPz⟩ := (hz' c).1
    obtain ⟨G, hG, hGe⟩ := (GlobalTheory.LvT.Built.ValLat.mem_intSpan_iff (I.rec7 l Z) w _ (I.perIn u a).sgT
      (fun τ => (GlobalTheory.PerQ.Co.PtInt.natW_sgT I u a τ).symm) _).1 (hco c)
    have hGV : G ∈ Formalism.L2.DIV.VV B.fields.K (I.perIn u a).sgT := GlobalTheory.LvT.Built.ValLat.mem_VV_of_locP _ _ hG
    have hspec := GlobalTheory.T.localBasisRepLattice_integralCoords_spec I hI l u a w c
    refine ⟨rhoVr B.fields.emb (I.perIn u a).sgT (GlobalTheory.PerQ.Co.bP I u a w c) ⟨G, hGV⟩, ?_, ?_⟩
    · rw [← hPz]
      show fnOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (shiftOf (I.perIn u a).sgT) 1 P =
        fnOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (shiftOf (I.perIn u a).sgT) 1
          (MvPolynomial.map B.embLL (rhoVr B.fields.emb (I.perIn u a).sgT (GlobalTheory.PerQ.Co.bP I u a w c) ⟨G, hGV⟩).1)
      congr 1
      have e1 : (rhoVr B.fields.emb (I.perIn u a).sgT (GlobalTheory.PerQ.Co.bP I u a w c) ⟨G, hGV⟩).1 =
          actP (I.perIn u a).sgT (invTrK (embGL B.fields.emb (GlobalTheory.PerQ.Co.bP I u a w c))) G := rfl
      rw [e1]
      have e3 := GlobalTheory.LvT.Built.ValLat.map_actP B.embLL (I.perIn u a).sgT
        (invTrK (embGL B.fields.emb (GlobalTheory.PerQ.Co.bP I u a w c))) G
      rw [GlobalTheory.PerQ.Co.PtInt.invTrK_bc] at e3
      refine Eq.trans ?_ e3.symm
      refine Eq.trans ?_ (congrArg (actP (I.perIn u a).sgT
        (invTrK (embGL (embAt B.embLL B.fields.emb) (GlobalTheory.PerQ.Co.bP I u a w c)))) hGe)
      show P = actP (I.perIn u a).sgT (invTrK (embGL (embAt B.embLL B.fields.emb) (GlobalTheory.PerQ.Co.bP I u a w c)))
        (actP (I.perIn u a).sgT (invTrK (embGL (embAt B.embLL B.fields.emb) (GlobalTheory.PerQ.Co.bP I u a w c)⁻¹))
          (polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (shiftOf (I.perIn u a).sgT)
            (fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) (z c)))
      rw [← polyAction_mul, map_inv, map_inv, mul_inv_cancel, polyAction_one₂, ← hPz]
      have h := polOf_fnOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (shiftOf (I.perIn u a).sgT)
        (fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) P
      have e : (fun τ => ((fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)).1 τ)⁻¹) = 1 := funext fun τ => inv_one
      rw [e] at h
      exact h.symm
    · have hinv : rhoVr B.fields.emb (I.perIn u a).sgT (GlobalTheory.PerQ.Co.bP I u a w c)⁻¹
          (rhoVr B.fields.emb (I.perIn u a).sgT (GlobalTheory.PerQ.Co.bP I u a w c) ⟨G, hGV⟩) = ⟨G, hGV⟩ := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      rw [GlobalTheory.T.mem_locW_delAtr_iff' B.fields.emb B.embLL B.places (I.rec7 l Z).plEq (I.rec7 l Z).val_eq (I.perIn u a).sgT
        (I.perIn u a).sg (GlobalTheory.PerQ.Co.PtInt.natW_sgT I u a) _ (hOk.lsh_lat c.1 _) w _ hspec.1, hinv]
      have h := hco c
      rw [hGe] at h
      exact h
  choose v hv1 hv2 using key
  obtain ⟨y, hy1, hy2⟩ := GlobalTheory.T.exists_hermitianForm_descent_coefficientField B.fields.emb B.embLL (I.perIn u a).S' (I.perIn u a).sgT (l.fmL u a).famP z hz' v hv1
  refine ⟨y, ?_, hy2⟩
  show y ∈ locW B.places w ((I.perIn u a).S'.hlat B.fields.emb (I.perIn u a).sgT (l.fmL u a).famP).L
  rw [GlobalTheory.T.mem_locW_hlat_iff' B.fields.emb B.places (I.rec7 l Z).plEq (I.rec7 l Z).val_eq (I.perIn u a).S' (I.perIn u a).sgT
    (l.fmL u a).famP hOk w y]
  intro c
  rw [hy1 c]
  exact hv2 c
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FourierInversion
section
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.SWQ

theorem fourier_inversion : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ)
    (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a →
    ∀ Φ : (Fin N → AF F) → ℂ, Decay Φ → Decay (Fo ψ ν a Φ) → Decay (Fo ψ ν a (Fo ψ ν a Φ)) →
      Fo ψ ν a (Fo ψ ν a Φ) = Da (-1) Φ := by
  intro F _ _ N ψ lam ν a hC Φ hΦ hFΦ hFFΦ
  have hD1 : Decay (Da (-1) Φ) :=
    (GlobalTheory.SWQ.decay_ops F N ψ lam ν a hC Φ hΦ).2.2.1 (-1) isUnit_one.neg
  apply GlobalTheory.T.eq_of_theta_heisenbergTranslates F N ψ lam ν a hC _ _ hFFΦ hD1
  intro x y

  have iΦ := GlobalTheory.SWQ.weil_intertwine F N ψ lam ν a hC Φ
  have iFΦ := GlobalTheory.SWQ.weil_intertwine F N ψ lam ν a hC (Fo ψ ν a Φ)
  have e1 : rho ψ a (-y) x (Fo ψ ν a Φ) = Fo ψ ν a (rho ψ a (-x) (-y) Φ) := by
    have := iΦ.2.2.1 (-y) x
    simpa using this
  have e2 : rho ψ a x y (Fo ψ ν a (Fo ψ ν a Φ)) = Fo ψ ν a (Fo ψ ν a (rho ψ a (-x) (-y) Φ)) := by
    rw [iFΦ.2.2.1 x y, e1]
  have dΨ : Decay (rho ψ a (-x) (-y) Φ) := (GlobalTheory.SWQ.decay_ops F N ψ lam ν a hC Φ hΦ).2.1 _ _
  have dFΨ : Decay (Fo ψ ν a (rho ψ a (-x) (-y) Φ)) := by
    rw [← e1]; exact (GlobalTheory.SWQ.decay_ops F N ψ lam ν a hC _ hFΦ).2.1 _ _
  have dFFΨ : Decay (Fo ψ ν a (Fo ψ ν a (rho ψ a (-x) (-y) Φ))) := by
    rw [← e2]; exact (GlobalTheory.SWQ.decay_ops F N ψ lam ν a hC _ hFFΦ).2.1 _ _
  rw [e2, GlobalTheory.T.poisson_summation_adelic_tuples F N ψ lam ν a hC _ dFΨ dFFΨ, GlobalTheory.T.poisson_summation_adelic_tuples F N ψ lam ν a hC _ dΨ dFΨ]

  have e3 : rho ψ a x y (Da (-1) Φ) = Da (-1) (rho ψ a (-x) (-y) Φ) := by
    have := iΦ.2.1 (-1) (-1) x y (by norm_num)
    simpa using this
  rw [e3]
  have e4 : (Da (-1 : AF F) (rho ψ a (-x) (-y) Φ) : (Fin N → AF F) → ℂ) =
      Da (algebraMap F (AF F) (-1)) (rho ψ a (-x) (-y) Φ) := by simp
  rw [e4, (GlobalTheory.SWQ.weil_intertwine F N ψ lam ν a hC (rho ψ a (-x) (-y) Φ)).2.2.2.2 (-1) (by norm_num)]

end GlobalTheory.SWQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HyperplaneFormIntegralLocalCoordsMemIntegralSpan
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PtIntCoord

theorem natW_shW {n : ℕ} (l : DomWeight n) (c : ℤ) : (GlobalTheory.Mem.Col2.shW l c).natW = l.natW := by
  have e : GlobalTheory.Mem.Col2.shW l c = Formalism.MainNotions.product_first_zeroth_parts.wSh l (-c) := by
    unfold GlobalTheory.Mem.Col2.shW Formalism.MainNotions.product_first_zeroth_parts.wSh
    congr 1
    funext i
    ring
  rw [e, Formalism.MainNotions.product_first_zeroth_parts.natW_wSh]

theorem coP_mem_intSpan : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι) (w : B.places.Pl), ∀ z ∈ ((I.tw l l0 Z).fm u a).ptC, (∃ y ∈ ((I.tw l l0 Z).fm u a).SP w, ((I.tw l l0 Z).fm u a).ptEmb y = z) → ∀ c, GlobalTheory.PerQ.Co.coP I u a w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan (I.rec7 l Z) w ((I.rec7 l Z).fm u).sg := by
  intro B X I hI l Z l0 u a w z _hz hyz c
  obtain ⟨y, hy, rfl⟩ := hyz
  clear _hz
  have hQ : (I.perIn u a).Ok := l.per u a
  have hA : y.1 c ∈ locW B.places w (delAtr B.fields.emb (I.perIn u a).sgT
      ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c))) := by
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (hx c)
    | zero => exact Submodule.zero_mem _
    | add x x' _ _ hx hx' => exact Submodule.add_mem _ hx hx'
    | smul r x _ hx => exact Submodule.smul_mem _ r hx
  have hB := (GlobalTheory.T.localBasisRepLattice_integralCoords_spec I hI l u a w c).1
  have key := (GlobalTheory.T.mem_locW_delAtr_iff' B.fields.emb B.embLL B.places (I.rec7 l Z).plEq (I.rec7 l Z).val_eq
    (I.perIn u a).sgT (I.perIn u a).sg (fun τ => natW_shW _ _) _ (hQ.step.lsh_lat c.1 _) w _ hB (y.1 c)).1 hA
  have e : GlobalTheory.PerQ.Co.coP I u a w (((I.tw l l0 Z).fm u a).ptEmb y) c =
      MvPolynomial.map B.embLL (rhoVr B.fields.emb (I.perIn u a).sgT (GlobalTheory.PerQ.Co.bP I u a w c)⁻¹ (y.1 c)).1 := by
    show actP _ _ (polOf _ _ _ (evV B.fields.emb 1 (I.perIn u a).sgT B.embLL (y.1 c))) = _
    rw [GlobalTheory.LvT.BuiltChain.polOf_evV]
    show _ = MvPolynomial.map B.embLL (actP (I.perIn u a).sgT
      (invTrK (Formalism.L2.DIV.embGL B.fields.emb (GlobalTheory.PerQ.Co.bP I u a w c)⁻¹)) (y.1 c).1)
    rw [GlobalTheory.ValCmp.use₂]
    congr 2
  rw [e]
  exact key

end GlobalTheory.PtIntCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LastStepIntegralFormLocalCoordsMemIntegralSpan
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
  GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerQ.Co

theorem bc_invTrK_embGL {B : Base} {n : ℕ} (g : GL (Fin n) B.fields.E) :
  (fun τ => Formalism.UG.bc B.embLL (invTrK (embGL B.fields.emb g) τ)) = invTrK (embGL (Formalism.L2.Col.embAt B.embLL B.fields.emb) g) := by
  funext τ
  apply Units.ext
  ext i j
  simp [invTrK, inside₂, embGL, Formalism.UG.bc, Formalism.L2.Col.embAt]
  rw [← Matrix.map_map, ← Formalism.L2.Col.map_inv_matrix, ← Formalism.L2.Col.map_inv_matrix, ← Formalism.L2.Col.map_inv_matrix]
  rfl

theorem intSpan_smul (D : D7) {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n) (r : D.what₂.LL)
    (hr : r ∈ intW D.what₂.places w) (p : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ)
    (hp : p ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w lam) : D.what₂.embLL r • p ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w lam := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.IntSpan at *
  induction hp using AddSubgroup.closure_induction with
  | mem q hq =>
    obtain ⟨r', f, hr', hf, rfl⟩ := hq
    apply AddSubgroup.subset_closure
    exact ⟨r * r', f, mul_mem hr hr', hf, by rw [map_mul, mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add p q _ _ hp hq => rw [smul_add]; exact add_mem hp hq
  | neg p _ hp => rw [smul_neg]; exact neg_mem hp

theorem latCo_one {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) (w : B.places.Pl) (c : (I.perIn u a).S'.Cl)
    (y : (((I.chIn u a).S B.R.m).hlat B.fields.emb (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m)).V) (hy : y ∈ (((I.chIn u a).S B.R.m).hlat B.fields.emb (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m)).L) :
    GlobalTheory.PerQ.Co.coM I u a w c (((I.chIn u a).S B.R.m).embF B.fields.emb B.embLL (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m) y ((I.perIn u a).tilC c)) ∈
      Formalism.MainNotions.product_first_zeroth_parts.IntSpan (I.rec7 l Z) w (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m) := by
  set v' := ((I.chIn u a).S B.R.m).rho B.fields.emb (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) (I.perIn u a).b0 (((I.chIn u a).S B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c))
          (y.1 (((I.chIn u a).S B.R.m).cl (I.perIn u a).b0 ((I.perIn u a).tilPt c))) with hv'
  have hmem := GlobalTheory.LvT.BuiltChain.rho_mv_mem B.fields.emb ((I.chIn u a).S B.R.m) (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m) y hy (I.perIn u a).b0 ((I.perIn u a).tilPt c)
  have e1 : GlobalTheory.PerQ.Co.coM I u a w c (((I.chIn u a).S B.R.m).embF B.fields.emb B.embLL (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m) y ((I.perIn u a).tilC c)) =
      actP (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) (invTrK (embGL (Formalism.L2.Col.embAt B.embLL B.fields.emb) (GlobalTheory.PerQ.Co.bM I u a w c)⁻¹))
        (MvPolynomial.map B.embLL v'.1) := by
    unfold GlobalTheory.PerQ.Co.coM
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    congr 1
    rw [← GlobalTheory.LvT.BuiltChain.polOf_evV B.fields.emb B.embLL]
    congr 1
    rw [hv', GlobalTheory.LvT.BuiltChain.evV_rho]
    rfl
  rw [e1, ← bc_invTrK_embGL, ← GlobalTheory.ValCmp.use₂]
  have hB := (GlobalTheory.T.localBasisRepLattice_integralCoords_spec I hI l u a w c).2.2.2
  have hM : Submodule.IsLattice B.fields.E (((I.chIn u a).S B.R.m).Lsh (I.perIn u a).b0 ((I.perIn u a).tilPt c)) :=
    ((l.ch u a).step B.R.m).lsh_lat (I.perIn u a).b0 ((I.perIn u a).tilPt c)
  have hnat : ∀ τ, ((GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) τ).natW = (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m τ).natW := by
    intro τ
    show (GlobalTheory.Mem.Col2.shW (Examples₂.lamOf (B.hcW u τ) B.R.m) _).natW = (Examples₂.lamOf (B.hcW u τ) B.R.m).natW
    funext i
    have hN : 0 < B.R.N B.R.m := lt_of_le_of_lt (Nat.zero_le _) i.2
    simp only [DomWeight.natW, DomWeight.detShift, dif_pos hN, GlobalTheory.Mem.Col2.shW]
    congr 1
    ring
  exact (GlobalTheory.T.mem_locW_delAtr_iff' B.fields.emb B.embLL B.places (I.rec7 l Z).plEq (I.rec7 l Z).val_eq
    (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m) hnat _ hM w _ hB v').1 (Submodule.subset_span hmem)

theorem latCo_gen {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) (w : B.places.Pl) (c : (I.perIn u a).S'.Cl) :
    ∀ x ∈ Submodule.span (intW B.places w) ((((I.chIn u a).S B.R.m).hlat B.fields.emb (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m)).L : Set (((I.chIn u a).S B.R.m).hlat B.fields.emb (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m)).V),
      GlobalTheory.PerQ.Co.coM I u a w c (((I.chIn u a).S B.R.m).embF B.fields.emb B.embLL (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m) x ((I.perIn u a).tilC c)) ∈
        Formalism.MainNotions.product_first_zeroth_parts.IntSpan (I.rec7 l Z) w (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m) := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy => exact latCo_one I hI l Z u a w c y hy
  | zero => rw [map_zero, Pi.zero_apply, map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add, Pi.add_apply, map_add]; exact add_mem hy hz
  | smul r y _ hy =>
    have e : r • y = (r : B.LL) • y := rfl
    rw [e, LinearMap.map_smulₛₗ, Pi.smul_apply, map_smul]
    exact intSpan_smul (I.rec7 l Z) w _ (r : B.LL) r.2 _ hy

theorem latCo_mem_intSpan : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι) (w : B.places.Pl), ∀ x ∈ ((I.tw l l0 Z).fm u a).S (I.rec7 l Z).R.m w, ∀ c, GlobalTheory.PerQ.Co.coM I u a w c (((I.tw l l0 Z).fm u a).emb (I.rec7 l Z).R.m x (((I.tw l l0 Z).fm u a).til c)) ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan (I.rec7 l Z) w (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m) :=
  fun I hI l Z _ u a w x hx c => latCo_gen I hI l Z u a w c x hx

end GlobalTheory.PerQ.Co

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalCoordsEvaluationLowerRowMapEqTensorBranchin
section
noncomputable section

namespace GlobalTheory.PerQ.Co

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr
  GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem coP_PtT_eq_blk : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι) (w : B.places.Pl), ∀ φ ∈ ((I.tw l l0 Z).fm u a).Fi (I.rec7 l Z).R.m, ∀ c, GlobalTheory.PerQ.Co.coP I u a w (GlobalTheory.PerQ.PtT (I.rec7 l Z) u a φ) c = Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ (I.rec7 l Z).R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ) (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ)) (GlobalTheory.PerQ.Co.coM I u a w c (φ (((I.tw l l0 Z).fm u a).til c))) := by
  intro B X I hI l Z l0 u a w φ hφ c
  have hV : φ ((I.perIn u a).tilC c) ∈ ValC (Gr B.fields.emb B.embLL (B.R.N B.R.m)) (lamT (B.hcW u) B.R.m) := (hφ _).1
  have hT : ((I.stp u a B.R.m).trTo B.fields.emb B.embLL (I.perIn u a).b0 ((I.perIn u a).tilPt c)) (φ ((I.perIn u a).tilC c)) ∈
      ValC (Gr B.fields.emb B.embLL (B.R.N B.R.m)) (lamT (B.hcW u) B.R.m) :=
    GlobalTheory.LvT.Built.RealM.trFr_mem _ _ _ _ _ hV
  obtain ⟨F, hF⟩ := (GlobalTheory.TilClass.mem_ValC_iff _ _ _ _).1 hT
  have hW := fun τ => GlobalTheory.T.trueWeights_eq_descentShiftedWeights_interlace I hI l Z u a τ
  have hS := GlobalTheory.T.localBasisRepLattice_integralCoords_spec I hI l u a w c
  show actP (I.perIn u a).sgT (invTrK ((embGL (embAt B.embLL B.fields.emb)) (GlobalTheory.PerQ.Co.bP I u a w c)⁻¹))
      (polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (shiftOf (I.perIn u a).sgT) (fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1))
        (fnOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (shiftOf (I.perIn u a).sgT) 1
          ((I.perIn u a).br B.fields.emb B.embLL (B.hcW u)
            (polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (lamT (B.hcW u) B.R.m)) (fr0 B.fields.emb B.embLL (B.R.N B.R.m))
              (((I.stp u a B.R.m).trTo B.fields.emb B.embLL (I.perIn u a).b0 ((I.perIn u a).tilPt c)) (φ ((I.perIn u a).tilC c))))))) =
    Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ B.R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ) (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ))
      (actP (lamT (B.hcW u) B.R.m) (invTrK ((embGL (embAt B.embLL B.fields.emb)) (GlobalTheory.PerQ.Co.bM I u a w c)⁻¹))
        (polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (lamT (B.hcW u) B.R.m)) (fr0 B.fields.emb B.embLL (B.R.N B.R.m))
          (((I.stp u a B.R.m).trTo B.fields.emb B.embLL (I.perIn u a).b0 ((I.perIn u a).tilPt c)) (φ ((I.perIn u a).tilC c)))))

  rw [← hF, GlobalTheory.TilClass.polOf_fnOf_one, GlobalTheory.TilClass.polOf_fnOf_one]
  have hlam : Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u = lamT (B.hcW u) B.R.m := funext fun τ => (hW τ).1
  have hsg : Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u = (I.perIn u a).sgT := funext fun τ => (hW τ).2.1
  refine Eq.trans ?_ (GlobalTheory.Proof.FockBlockMonotone.blk_brOne_eq (ι := B.fields.Tau) (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ B.R).symm _ _ _).symm
  rw [hlam, hsg]
  have key := GlobalTheory.BranchBlock.rhoVr_brAt_eq_brStd (embAt B.embLL B.fields.emb) (N_m_succ B.R) (lamT (B.hcW u) B.R.m)
    (I.perIn u a).sgT (fun τ => (hW τ).2.2.1) (fun τ => (hW τ).2.2.2.1) (I.perIn u a).tz _ _ hS.2.1 hS.2.2.1 F
  exact congrArg Subtype.val key

end GlobalTheory.PerQ.Co

end
end

