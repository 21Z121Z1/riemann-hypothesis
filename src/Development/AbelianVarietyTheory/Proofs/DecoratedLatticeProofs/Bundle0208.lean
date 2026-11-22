import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0339
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0338
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0188
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0171
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0237
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0139
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0189
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionStar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0269
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0190
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearIndependentOfIsParamFunV
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem linearIndependent_of_isParamFunV : ∀ (D : D7) (V : HSp D) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (ι : Type)
    (f : ι → (GA D V → ℂ)) (B : ι → GlobalTheory.LFun.Fam D.host.E), (∀ i, f i ≠ 0) → (∀ i, GlobalTheory.LFun.IsParamFunV V Sb (f i) (B i)) →
    (∀ i i', i ≠ i' → ∃ w ∉ GlobalTheory.LFun.above D.host.E (Sb : Set (HeightOneSpectrum (𝓞 D.host.F))), B i w ≠ B i' w) →
    LinearIndependent ℂ f := by
  intro D V Sb ι f B h0 hP hB
  have hJ := GlobalTheory.LFun.sphOff_KsphC V Sb
  choose a ha using fun i => GlobalTheory.T.sphericalOperator_eigenvalues_determined_by_params D V (KsphC V ∅) (fun _ => 1) Sb hJ (B i)
  have hfix : ∀ i, ∀ v ∉ Sb, ∀ k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (GlobalTheory.AdelicU.frameLat V) v, ∀ g,
      f i (g * GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v k) = f i g := by
    intro i v hv k hk g
    obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
      have := v.isPrime
      obtain ⟨Q, hQ, hl⟩ := (Ideal.nonempty_primesOver v.asIdeal (S := 𝓞 D.host.E)).some
      exact ⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
    have hx := (hP i v hv w hw).mem_fixed
    exact congrFun (GlobalTheory.LGrp.mem_fixed.1 hx k hk) g
  let α := {t : HeightOneSpectrum (𝓞 D.host.E) × List ℤ × Finset (GA D V) //
    Hecke₂ V (KsphC V ∅) (fun _ => 1) Sb t.1 t.2.1 t.2.2}
  refine GlobalTheory.FinWeil.linearIndependent_of_simultaneous_eigen f (fun i (t : α) => a i t.1.1 t.1.2.1)
    (fun t : α => heckeLin V t.1.2.2) ?_ (fun t i => ha i (f i) (hP i) _ _ _ t.2) h0
  intro i i' hii
  by_contra hne
  obtain ⟨w, hw, hne'⟩ := hB i i' hne
  have hc : ∀ P d R, Hecke₂ V (KsphC V ∅) (fun _ => 1) Sb P d R → heckeLin V R (f i') = a i P d • f i' := by
    intro P d R hR
    have := congrFun hii ⟨(P, d, R), hR⟩
    rw [ha i' (f i') (hP i') P d R hR]
    exact congrArg (· • f i') this.symm
  have h1 := (GlobalTheory.LFun.isParamFunV_iff_isSysParamD hJ (h0 i) (hfix i) (ha i (f i) (hP i)) (B i)).1 (hP i)
  have h2 := (GlobalTheory.LFun.isParamFunV_iff_isSysParamD hJ (h0 i') (hfix i') hc (B i')).1 (hP i')
  exact hne' (GlobalTheory.LFun.IsSysParamOff.unique h1 h2 hw)

end GlobalTheory.ChainOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearIndependentScaledBasisColumnsMatrixTranspoStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_scaledBasisColumnsMatrix_transpose : ∀ {D : D7} (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t lam : D.host.E), t ≠ 0 → lam ≠ 0 → LinearIndependent D.host.E (GlobalTheory.Core.SBesEx.eM X h t lam).transpose := by
  first | exact @GlobalTheory.Core.SBesEx.eM_transpose_linearIndependent | exact GlobalTheory.Core.SBesEx.eM_transpose_linearIndependent | (intros; apply GlobalTheory.Core.SBesEx.eM_transpose_linearIndependent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalGroupActionInertSupportedPointsFrames
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.InertFrameAct

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

theorem compW_eq_toCompl (h : w.under (𝓞 D.host.F) = v) (a : AE D) :
    GlobalTheory.InertHomIdx.compW D w a = toCompl h (GlobalTheory.AdelicU.compFin D.host.F D.host.E v a) := by
  show finAdEquiv D.host.F D.host.E (finPart D a) w = _
  rw [finAdEquiv_apply h, ← GlobalTheory.EmbChart.map_evalV_map_sndA]
  rfl

theorem secW_mul (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (z : w.adicCompletion D.host.E) (a : AE D) :
    secW hw h z * a = secW hw h (z * GlobalTheory.InertHomIdx.compW D w a) := by
  show GlobalTheory.EmbChart.tensAt D.host.E v ((InertChart.complEquiv hw h).symm z) * a =
    GlobalTheory.EmbChart.tensAt D.host.E v ((InertChart.complEquiv hw h).symm (z * GlobalTheory.InertHomIdx.compW D w a))
  rw [GlobalTheory.EmbChart.tensAt_mul_right]
  congr 1
  apply (InertChart.complEquiv hw h).injective
  rw [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, compW_eq_toCompl h]
  rfl

theorem mul_secW (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (z : w.adicCompletion D.host.E) (a : AE D) :
    a * secW hw h z = secW hw h (GlobalTheory.InertHomIdx.compW D w a * z) := by
  rw [mul_comm, secW_mul, mul_comm]

theorem mul_map_secW (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) (AE D)) (M : Matrix (Fin n) (Fin p) (w.adicCompletion D.host.E)) :
    A * M.map (secW hw h) = (A.map (GlobalTheory.InertHomIdx.compW D w) * M).map (secW hw h) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, mul_secW]

theorem map_secW_mul (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) {m n p : ℕ}
    (M : Matrix (Fin m) (Fin n) (w.adicCompletion D.host.E)) (B : Matrix (Fin n) (Fin p) (AE D)) :
    M.map (secW hw h) * B = (M * B.map (GlobalTheory.InertHomIdx.compW D w)).map (secW hw h) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, secW_mul]

end GlobalTheory.InertFrameAct

open GlobalTheory.InertFrameAct in

theorem GlobalTheory.InertFrameAct.actO_uPt : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (S T : HSp D) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)) (gS : Gv S v) (gT : Gv T v) (x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E)), actO S T (embV S v gS) (embV T v gT) (uPt hw h k aS aT x) = uPt hw h k aS aT ((aT⁻¹ * locMat D.sp.cm.sig T.gram h gT * aT).1 * x * (aS⁻¹ * locMat D.sp.cm.sig S.gram h gS⁻¹ * aS).1) := by
  intro D v w hw h S T k aS aT gS gT x
  have hT : (mt T (embV T v gT)).map (GlobalTheory.InertHomIdx.compW D w) = (locMat D.sp.cm.sig T.gram h gT).1 := by
    have e := finMat_map_compAt D.sp.cm.sig T.gram h (embV T v gT)
    rw [proj_emb_self] at e
    exact e
  have hS : (mt S (embV S v gS⁻¹)).map (GlobalTheory.InertHomIdx.compW D w) = (locMat D.sp.cm.sig S.gram h gS⁻¹).1 := by
    have e := finMat_map_compAt D.sp.cm.sig S.gram h (embV S v gS⁻¹)
    rw [proj_emb_self] at e
    exact e
  have hinv : (embV S v gS)⁻¹ = embV S v gS⁻¹ := (map_inv _ _).symm
  rw [actO, uPt, uPt, hinv, mul_map_secW, map_secW_mul, hT, hS]
  congr 1
  have h1 : aT.1 * (aT⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : aS.1 * (aS⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Units.val_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [h2, Matrix.mul_one]
  rw [← Matrix.mul_assoc aT.1 (aT⁻¹).1, h1, Matrix.one_mul]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelRestrictedToLineSlice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SliceLine

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem ι_mul (x : k) (b : AE D) : p.ι x * b = p.ι (x * p.π b) := by
  have h : p.ι (x * p.π b) = p.e * (p.ι x * b) := by
    calc p.ι (x * p.π b) = p.ι (p.π (p.ι x) * p.π b) := by rw [p.π_ι]
      _ = p.ι (p.π (p.ι x * b)) := by rw [p.π.map_mul]
      _ = p.e * (p.ι x * b) := p.ι_π _
  rw [h, ← mul_assoc, GlobalTheory.LocMod.Witness.e_ι]

theorem map_ι_mul {a b c : Type} [Fintype b] (M : Matrix a b k) (N : Matrix b c (AE D)) :
    M.map p.ι * N = (M * N.map p.π).map p.ι := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, ι_mul]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem frame_card {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y) : Fintype.card Y = N := by
  have e : (Y → k) ≃ₗ[k] (Fin N → k) := LinearEquiv.ofLinear (Matrix.toLin' F.β) (Matrix.toLin' F.γ)
    (by rw [← Matrix.toLin'_mul, F.βγ, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, F.γβ, Matrix.toLin'_one])
  simpa using e.finrank_eq

def splitCols (n n' : Type) : Matrix n (n' ⊕ Unit) k ≃ₜ Matrix n n' k × Matrix n Unit k where
  toFun x := (x.toCols₁, x.toCols₂)
  invFun q := fromCols q.1 q.2
  left_inv x := fromCols_toCols x
  right_inv q := by simp
  continuous_toFun := by
    refine Continuous.prodMk ?_ ?_
    · exact continuous_matrix fun i j => continuous_id.matrix_elem i (Sum.inl j)
    · exact continuous_matrix fun i j => continuous_id.matrix_elem i (Sum.inr j)
  continuous_invFun := by
    refine continuous_matrix fun i j => ?_
    cases j with
    | inl a => exact continuous_fst.matrix_elem i a
    | inr u => exact continuous_snd.matrix_elem i u

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def box (Ξ : SB (Matrix n n' k)) : SB (Matrix n Unit k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) where
  toFun c := comapH (splitCols n n') (prodSB Ξ c)
  map_add' c c' := Subtype.ext (funext fun x => by simp [splitCols, mul_add])
  map_smul' a c := Subtype.ext (funext fun x => by simp [splitCols]; ring)

theorem box_apply (Ξ : SB (Matrix n n' k)) (c : SB (Matrix n Unit k)) (x : Matrix n (n' ⊕ Unit) k) :
    (box Ξ c).1 x = Ξ.1 x.toCols₁ * c.1 x.toCols₂ := rfl

end GlobalTheory.SliceLine

namespace GlobalTheory.SliceLine

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem heis_slice {S A L T : HSp D} (d : OrthDec S A L) (ψ : AddChar (AF D.host.F) ℂ) (f : WO S T → ℂ)
    (u : WO A T) (w v : WO L T) :
    heisO ψ S T ((d.resS T).symm (0, v)) f ((d.resS T).symm (u, w)) =
      heisO ψ L T v (fun w => f ((d.resS T).symm (u, w))) w := by
  simp only [heisO]
  rw [d.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, zero_add,
    ← map_add, Prod.mk_add_mk, add_zero]

theorem symplO_zero_right' (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  simp [symplO, hO]

theorem isHalf_slice {S A L T : HSp D} (d : OrthDec S A L) {a : AE D} {y : WO L T} (hy : IsHalf a y) :
    IsHalf a ((d.resS T).symm (0, y)) := by
  intro i j
  rw [resS_symm_apply, Matrix.zero_mul, zero_add, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← mul_assoc, hy i l]

variable {ρ : ℕ} {B : BesLev D ρ} {s : k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {FA : Frame k B.A.rank n'} {F₀ : Frame k B.V₀.rank (n' ⊕ Unit)} {FL : Frame k B.L.rank Unit}

theorem beta_eq (h : p.IsCoreFrame B s FA F₀) (hL : ∀ r, FL.β r () = s * p.pr (B.ζ r)) :
    F₀.β = fromCols (B.o.iA.map (p.π.comp (incA D)) * FA.β) (B.o.iB.map (p.π.comp (incA D)) * FL.β) := by
  ext r (a | u)
  · exact h.1 r a
  · cases u
    rw [h.2 r, fromCols_apply_inr, Matrix.mul_apply]
    simp only [vecB, Matrix.mulVec, dotProduct, Place.pr, map_sum, map_mul, Matrix.map_apply, hL, RingHom.comp_apply,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

end GlobalTheory.SliceLine

namespace GlobalTheory.SliceLine

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
variable {ρ : ℕ} {B : BesLev D ρ} {s : k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {FA : Frame k B.A.rank n'} {F₀ : Frame k B.V₀.rank (n' ⊕ Unit)} {FL : Frame k B.L.rank Unit}

theorem rat_map_π {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E) : (rat M).map p.π = M.map (p.π.comp (incA D)) := rfl

theorem up_fromCols (h : p.IsCoreFrame B s FA F₀) (hL : ∀ r, FL.β r () = s * p.pr (B.ζ r)) {S : HSp D}
    (FS : Frame k S.rank n) (x : Matrix n Unit k) :
    p.up F₀ FS (fromCols 0 x) = (B.o.resS S).symm (0, p.up FL FS x) := by
  have k1 : x * FL.γ * B.o.qB.map (p.π.comp (incA D)) * F₀.β = fromCols (0 : Matrix n n' k) x := by
    rw [beta_eq p h hL, Matrix.mul_fromCols]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (B.o.qB.map _) (B.o.iA.map _), ← Matrix.map_mul, B.o.qB_iA,
      ← Matrix.mul_assoc (B.o.qB.map _) (B.o.iB.map _), ← Matrix.map_mul, B.o.qB_iB]
    simp [FL.γβ]
  have k2 : fromCols (0 : Matrix n n' k) x * F₀.γ = x * FL.γ * B.o.qB.map (p.π.comp (incA D)) := by
    rw [← k1, Matrix.mul_assoc (x * FL.γ * B.o.qB.map (p.π.comp (incA D))) F₀.β F₀.γ, F₀.βγ, Matrix.mul_one]
  rw [resS_symm_apply, Matrix.zero_mul, zero_add]
  unfold Place.up
  rw [pB, map_ι_mul, rat_map_π]
  congr 1
  rw [Matrix.mul_assoc FS.β (fromCols 0 x) F₀.γ, k2]
  simp only [Matrix.mul_assoc]

theorem resS_up_snd (h : p.IsCoreFrame B s FA F₀) (hL : ∀ r, FL.β r () = s * p.pr (B.ζ r)) {S : HSp D}
    (FS : Frame k S.rank n) (t : Matrix n (n' ⊕ Unit) k) :
    (B.o.resS S (p.up F₀ FS t)).2 = p.up FL FS t.toCols₂ := by
  have k1 : t * F₀.γ * B.o.iB.map (p.π.comp (incA D)) * FL.β = t.toCols₂ := by
    calc t * F₀.γ * B.o.iB.map (p.π.comp (incA D)) * FL.β
        = ((t * F₀.γ) * fromCols (B.o.iA.map (p.π.comp (incA D)) * FA.β)
            (B.o.iB.map (p.π.comp (incA D)) * FL.β)).toCols₂ := by
          rw [Matrix.mul_fromCols, toCols₂_fromCols, Matrix.mul_assoc (t * F₀.γ)]
      _ = ((t * F₀.γ) * F₀.β).toCols₂ := by rw [← beta_eq p h hL]
      _ = t.toCols₂ := by rw [Matrix.mul_assoc, F₀.γβ, Matrix.mul_one]
  have k2 : t * F₀.γ * B.o.iB.map (p.π.comp (incA D)) = t.toCols₂ * FL.γ := by
    rw [← k1, Matrix.mul_assoc (t * F₀.γ * B.o.iB.map (p.π.comp (incA D))) FL.β FL.γ, FL.βγ, Matrix.mul_one]
  rw [resS_apply]
  dsimp only
  unfold Place.up
  rw [jB, map_ι_mul, rat_map_π]
  simp only [Matrix.mul_assoc] at k2 ⊢
  rw [k2]

end GlobalTheory.SliceLine

namespace GlobalTheory.SliceLine

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac

theorem toCols_add {k n n' : Type} [Field k] (t : Matrix n (n' ⊕ Unit) k) (x : Matrix n Unit k) :
    (t + fromCols (0 : Matrix n n' k) x).toCols₁ = t.toCols₁ ∧ (t + fromCols (0 : Matrix n n' k) x).toCols₂ = t.toCols₂ + x :=
  ⟨by ext i j; simp, by ext i j; simp⟩

theorem slice_line : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ F₀ FS T₀ → ∃ FL : Frame k B.L.rank Unit, (∀ r, FL.β r () = s * p.pr (B.ζ r)) ∧ ∀ (Ξ : SB (Matrix n n' k)) (u₀ : WO B.A S), ∃ T', p.IsModel ψ FL FS T' ∧ ∀ (c : SB (Matrix n Unit k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), (∀ x, Ψ.1 x = Ξ.1 x.toCols₁ * c.1 (Matrix.of fun r _ => x r (Sum.inr ()))) → ∀ w, T' c w = T₀ Ψ ((B.o.resS S).symm (u₀, w)) := by
  intro D k _ _ _ _ p ψ ρ B S s n n' _ _ _ _ FA F₀ FS h T₀ hT
  have hA := frame_card FA
  have h0 := frame_card F₀
  have hr := B.o.rank_add
  rw [Fintype.card_sum, Fintype.card_unit] at h0
  have hL1 : B.L.rank = 1 := by omega
  have hsub : ∀ r r' : Fin B.L.rank, r = r' := fun r r' => Fin.ext (by have := r.isLt; have := r'.isLt; omega)
  have hv : ∀ r, s * p.pr (B.ζ r) ≠ 0 := by
    intro r₀ h₀
    have hz : ∀ r, s * p.pr (B.ζ r) = 0 := fun r => by rw [hsub r r₀]; exact h₀
    have hcol : ∀ r, F₀.β r (Sum.inr ()) = 0 := by
      intro r
      rw [h.2 r]
      simp only [vecB, Matrix.mulVec, dotProduct, Place.pr, map_sum, map_mul, Finset.mul_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      have := hz j
      simp only [Place.pr] at this
      rw [mul_left_comm, this, mul_zero]
    have := congrFun (congrFun F₀.γβ (Sum.inr ())) (Sum.inr ())
    simp [Matrix.mul_apply, hcol] at this
  obtain ⟨FL, hFL⟩ : ∃ FL : Frame k B.L.rank Unit, ∀ r, FL.β r () = s * p.pr (B.ζ r) := by
    refine ⟨⟨Matrix.of fun r _ => s * p.pr (B.ζ r), Matrix.of fun _ r => (s * p.pr (B.ζ r))⁻¹, ?_, ?_⟩, fun r => rfl⟩
    · ext r r'
      obtain rfl := hsub r r'
      simp [Matrix.mul_apply]
      rw [← _root_.mul_inv_rev]
      exact mul_inv_cancel₀ (hv r)
    · ext u u'
      simp [Matrix.mul_apply]
      rw [Finset.sum_congr rfl (g := fun _ => (1 : k)) fun j _ => by rw [← _root_.mul_inv_rev]; exact inv_mul_cancel₀ (hv j)]
      simp [hL1]
  refine ⟨FL, hFL, fun Ξ u₀ => ?_⟩
  let T' : SB (Matrix n Unit k) →ₗ[ℂ] (WO B.L S → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (fun w : WO B.L S => (B.o.resS S).symm (u₀, w))).comp (T₀.comp (box Ξ))
  have hT' : ∀ c w, T' c w = T₀ (box Ξ c) ((B.o.resS S).symm (u₀, w)) := fun _ _ => rfl
  refine ⟨T', ⟨fun Φ => ?_, fun x Φ Φ' hΦ => ?_, fun y hy Φ Φ' hΦ => ?_⟩, fun c Ψ hΨ w => ?_⟩
  · exact GlobalTheory.BoxSlice.isThetaFunO_slice_right B.o (hT.theta (box Ξ Φ)) u₀
  · have e := hT.trans (fromCols 0 x) (box Ξ Φ) (box Ξ Φ') (fun t => by
      rw [box_apply, box_apply, hΦ, (toCols_add t x).1, (toCols_add t x).2])
    funext w
    rw [hT', e, up_fromCols p h hFL, heis_slice]
    rfl
  · have e := hT.modul ((B.o.resS S).symm (0, y)) (isHalf_slice B.o hy) (box Ξ Φ) (box Ξ Φ') (fun t => by
      simp only [box_apply, hΦ, B.o.symplO_resS, AddEquiv.apply_symm_apply, resS_up_snd p h hFL, symplO_zero_right',
        zero_add]
      ring)
    funext w
    rw [hT', e, heis_slice]
    rfl
  · have e : Ψ = box Ξ c := Subtype.ext (funext fun x => by rw [hΨ, box_apply]; rfl)
    rw [hT', e]

end GlobalTheory.SliceLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MajorantExistsAndWittDecompositionStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.majorant_exists_and_witt_decomposition : ∀ (D : D7) (W : HSp D), HSpace.SigOK W → (∃ b : GL (Fin W.rank) (AE D), IsMaj W b) ∧ (IsAniso W ∨ ∃ (W₀ : HSp D) (r' : ℕ) (_ : HypDec W W₀ r'), IsAniso W₀ ∧ 0 < r') := by
  first | exact @GlobalTheory.Core.Rk.WittDec.maj_and_witt | exact GlobalTheory.Core.Rk.WittDec.maj_and_witt | (intros; apply GlobalTheory.Core.Rk.WittDec.maj_and_witt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MaximalCompactSortedFrameActsThroughModelCompactStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximal_compact_sorted_frame_acts_through_model_compact : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (hV : V.SigOK) (k : GA D V), IsInfFam θ → k ∈ GlobalTheory.Cusp.Kinf θ V (GlobalTheory.ChainOnto.RealData.sortedFrame M hV) → ∀ τ, M.fr τ * infMat D.sp.cm.sig V.gram (θ τ) k * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) := by
  first | exact @GlobalTheory.ChainOnto.RealData.conj_mem_Kset_of_mem_Kinf | exact GlobalTheory.ChainOnto.RealData.conj_mem_Kset_of_mem_Kinf | (intros; apply GlobalTheory.ChainOnto.RealData.conj_mem_Kset_of_mem_Kinf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHyperspecialSubgroupAtPlaceIffLocalStabilizerStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_hyperspecialSubgroupAtPlace_iff_local_stabilizer : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → ∀ (V : HSp D) (g : GA D V), g ∈ hyp V w ↔ ∃ k ∈ Kv V v, g = embV V v k := by
  first | exact @GlobalTheory.HypDict.mem_hyp_iff_embV | exact GlobalTheory.HypDict.mem_hyp_iff_embV | (intros; apply GlobalTheory.HypDict.mem_hyp_iff_embV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemWittStabilizerOfKeepsIsotropicRealPlacesStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.AdelicU Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_wittStabilizer_of_keeps_isotropic_real_places : ∀ {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (q : GA D T), q ∈ GinfC T → (∀ w : InfinitePlace D.host.F, ∃ β : Matrix (Fin r) (Fin r) (TensorProduct D.host.F w.Completion D.host.E), (matHom _ D.sp.cm.sig T.gram (projArch D.sp.cm.sig T.gram w q)).1 * Matrix.map d.jX (compInf D.host.F D.host.E w) = Matrix.map d.jX (compInf D.host.F D.host.E w) * β) → q ∈ stab d := by
  first | exact @GlobalTheory.Core.Rk.IwGlob.mem_stab_of_keeps | exact GlobalTheory.Core.Rk.IwGlob.mem_stab_of_keeps | (intros; apply GlobalTheory.Core.Rk.IwGlob.mem_stab_of_keeps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicityMapRightTranslateRealPointStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicity_map_right_translate_real_point : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T → ∀ k ∈ GinfC V, ∀ v : M.Vec, ∃ v' : M.Vec, (∀ τ, (v' τ : M.H τ) = M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) k) (v τ)) ∧ ∀ x, T v (x * k) = T v' x := by
  first | exact @GlobalTheory.RealPointMove.translate_eq_move | exact GlobalTheory.RealPointMove.translate_eq_move | (intros; apply GlobalTheory.RealPointMove.translate_eq_move <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrderDetOneAddOfIntegralInverseUnitaryStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.order_det_one_add_of_integral_inverse_unitary : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n : ℕ) (g t : GU σ n) (d : Fin n → ℤ), t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KU σ n, ∀ k₂ ∈ KU σ n, g⁻¹ = k₁ * t * k₂ → (1 + g.1.1).det ≠ 0 → (1 + g.1.1)⁻¹ ∈ intMat L (Fin n) (Fin n) → ordL (1 + g.1.1).det = -∑ i, max (d i) 0 := by
  first | exact @GlobalTheory.ChainOnto.ordL_det_one_add_of_inv_int | exact GlobalTheory.ChainOnto.ordL_det_one_add_of_inv_int | (intros; apply GlobalTheory.ChainOnto.ordL_det_one_add_of_inv_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalIsometryKeepsIsotropicFrameOfSiegelStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.Dich
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_isometry_keeps_isotropic_frame_of_siegel : ∀ (D : D7) (V : HSp D), ∀ γ ∈ GQ (dblSp V), ∀ γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E, (matHom (dblSp V) γ⁻¹).1 = γi.map (incA D) → ∀ (r : ℕ) (K : Matrix (Fin V.rank) (Fin r) D.host.E), diagSnd γi * K = 0 → (∀ x : Fin V.rank → D.host.E, diagSnd γi *ᵥ x = 0 → ∃ y, x = K *ᵥ y) → IsIsoFrame V (leviMat finSumFinEquiv γi * K) → ∀ δ ∈ GQ V, ∀ δ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E, (matHom V δ).1 = δ₀.map (incA D) → γ * io V (δ, 1) * γ⁻¹ ∈ siegel V → ∃ G : Matrix (Fin r) (Fin r) D.host.E, IsUnit G ∧ δ₀ * (leviMat finSumFinEquiv γi * K) = leviMat finSumFinEquiv γi * K * G := by
  first | exact @GlobalTheory.Core.Rk.Dich.isoFrame_keep | exact GlobalTheory.Core.Rk.Dich.isoFrame_keep | (intros; apply GlobalTheory.Core.Rk.Dich.isoFrame_keep <;> assumption)
end

