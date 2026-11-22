import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0737
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0736
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0527
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0553
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0303
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0734
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0300
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0570
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0738
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0667
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0697
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0586

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawDoublingHermitianFormStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_doubling_hermitian_form : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (θ : InfFam D) (X : HSp D) {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ q ∈ l, q.2 ∈ lieAt X q.1) →
    ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ₁D : (Fin a × Fin (a + a') → AF D.host.F) → ℂ,
    (∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) ΦD x) (Φ₁D x) 0) →
    ∃ Ψ : Fin l.length → (Fin a × Fin (a + a') → AF D.host.F) → ℂ,
      (∀ i, Ψ i ∈ algD Γ.M Bs.ψ Bs.emb ∧
        ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) ΦD x) (Ψ i x) 0) ∧
      Φ₁D = ∑ i, Ψ i := by
  first | exact @GlobalTheory.LineSum.derSum | exact GlobalTheory.LineSum.derSum | (intros; apply GlobalTheory.LineSum.derSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingSwapStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_unfolding_swap : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.V, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ₁D ∈ algD Γ.M Bs.ψ Bs.emb,
    (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) ΦD x) (Φ₁D x) 0) → ∀ Φ₁,
    IsDatum Γ.M ψ cA Φ₁D Φ₁ → p Φ₁ = 0 := by
  first | exact @GlobalTheory.LineKillV.lineV_kill | exact GlobalTheory.LineKillV.lineV_kill | (intros; apply GlobalTheory.LineKillV.lineV_kill <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceScalarsMulEqOppositePathEdgeFactorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceScalars_mul_eq_oppositePath_edgeFactors : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)),
    finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ w ∈ locPl G t, (∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e w) →
    GlobalTheory.RowVacScalar.splitScal G (.chi j D.R.m) w (G.toPair (.chi j D.R.m) 1 (moved S j k)).1
                 (G.toPair (.chi j D.R.m) 1 (moved S j k)).2 *
      GlobalTheory.RowVacScalar.splitScal G (.chi (j + 1) D.R.m) w (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1).1
        (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1).2 =
    ((oppositePath D.R.m).map ((locGrid G t w).edgeFactor .one (Pi.mulSingle (j + 1, D.R.m)
      (inBasis (rank_vertex G t w (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w
        (finG (G.V (.grid (j + 1) D.R.m)) k))))).prod := by
  first | exact @GlobalTheory.RowVacScalar.splitScal_mul_eq_oppositePath | exact GlobalTheory.RowVacScalar.splitScal_mul_eq_oppositePath | (intros; apply GlobalTheory.RowVacScalar.splitScal_mul_eq_oppositePath <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardLatticeOffS0
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.FinPlLoc (idem mem_idOff_iff idem_mul_self)
open GlobalTheory.AscFinWit (mem_latO_at idem_mem_latO mxAt_mul mxAt_mul')

noncomputable section

namespace GlobalTheory.AscFin.StdOff

theorem latO_le_negSp {D : D7} (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO S T LS LT P ≤ latO (negSp S) T LS LT P := by
  unfold latO
  rw [AddSubgroup.closure_le]
  rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  rw [← neg_neg (Matrix.of _)]
  refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem latO_negSp_le' {D : D7} (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO (negSp S) T LS LT P ≤ latO S T LS LT P := by
  unfold latO
  rw [AddSubgroup.closure_le]
  rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  rw [← neg_neg (Matrix.of _)]
  refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem depLat_iff_at {D : D7} {S T : HSp D} {LS : GlobalTheory.FinPl.Lat S} {LT : GlobalTheory.FinPl.Lat T}
    {v : GlobalTheory.FinPl.Pl D} {W0 : Finset (Formalism.L2.DIV.Pl D.host.E)} (hoff : ∀ PP ∈ W0, PP.under (𝓞 D.host.F) ≠ v)
    (H : AddSubgroup (WO S T)) {u : WO S T} (hu : MxAt (· = v) u) :
    (u ∈ latO (negSp S) T (LS : Set _) (LT : Set _) (fun _ => True) ∧ ∀ e : AE D, IsIdemSum e W0 → e • u ∈ H) ↔
      u ∈ latO S T (LS : Set _) (LT : Set _) (· = v) := by
  constructor
  · rintro ⟨h1, -⟩
    exact latO_negSp_le' S T _ _ _ ((mem_latO_at (S := negSp S) hu).1 h1)
  · intro h1
    refine ⟨(mem_latO_at (S := negSp S) hu).2 (latO_le_negSp S T _ _ _ h1), fun e he => ?_⟩
    have : e • u = 0 := Matrix.ext fun i j => (GlobalTheory.FinZeta.VacOff.idemSum_mul_off he hoff h1 i j).1
    rw [this]
    exact zero_mem _

theorem pair_tmul_scale {D : D7} (α' : Af D.host.F) (d : D.host.F) (X : D.host.E) :
    pairA D.host.F 0 (α' * algebraMap D.host.F (Af D.host.F) d) ⊗ₜ[D.host.F] X =
      pairA D.host.F 0 α' ⊗ₜ[D.host.F] ((d : D.host.E) * X) := by
  have e : (d : D.host.E) * X = d • X := rfl
  have e2 : pairA D.host.F 0 (α' * algebraMap D.host.F (Af D.host.F) d) = d • pairA D.host.F 0 α' := by
    refine Prod.ext ?_ ?_
    · show (0 : Ainf D.host.F) = d • (0 : Ainf D.host.F)
      rw [smul_zero]
    · show α' * algebraMap D.host.F (Af D.host.F) d = d • α'
      rw [Algebra.smul_def, mul_comm]
  rw [e, e2, ← TensorProduct.smul_tmul']
  exact ((TensorProduct.mk D.host.F (AF D.host.F) D.host.E (pairA D.host.F 0 α')).map_smul d X).symm

def gen {D : D7} (S U : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin U.rank → D.host.E) :
    WO S U :=
  Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)

theorem gen_zero {D : D7} (S U : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) :
    gen S U α a s 0 = 0 := by
  ext i j
  rw [gen, Matrix.of_apply, Matrix.zero_apply, Pi.zero_apply, mul_zero, zero_mul, TensorProduct.tmul_zero]

theorem gen_add {D : D7} (S U : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E)
    (t t' : Fin U.rank → D.host.E) : gen S U α a s (t + t') = gen S U α a s t + gen S U α a s t' := by
  ext i j
  rw [Matrix.add_apply, gen, gen, gen, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply, Pi.add_apply, mul_add, add_mul,
    TensorProduct.tmul_add]

theorem gen_smul {D : D7} (S U : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E)
    (c : 𝓞 D.host.E) (t : Fin U.rank → D.host.E) : gen S U α a s (c • t) = gen S U α (a * (c : D.host.E)) s t := by
  ext i j
  have hc : c • t i = (c : D.host.E) * t i := Algebra.smul_def c (t i)
  rw [gen, gen, Matrix.of_apply, Matrix.of_apply, Pi.smul_apply, hc, ← mul_assoc]

theorem gen_smulE {D : D7} (S U : HSp D) (α : Af D.host.F) (a b : D.host.E) (s : Fin S.rank → D.host.E)
    (t : Fin U.rank → D.host.E) : gen S U α a s (b • t) = gen S U α (a * b) s t := by
  ext i j
  rw [gen, gen, Matrix.of_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, ← mul_assoc]

theorem gen_scale {D : D7} (S U : HSp D) (α : Af D.host.F) (d : D.host.F) (a b : D.host.E) (s : Fin S.rank → D.host.E)
    (t : Fin U.rank → D.host.E) :
    gen S U (α * algebraMap D.host.F (Af D.host.F) d) a s (b • t) = gen S U α (a * ((d : D.host.E) * b)) s t := by
  ext i j
  rw [gen, gen, Matrix.of_apply, Matrix.of_apply, pair_tmul_scale, Pi.smul_apply, smul_eq_mul]
  congr 1
  ring

theorem latO_idLat_at {D : D7} (S U : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LU : GlobalTheory.FinPl.Lat U)
    (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (v : GlobalTheory.FinPl.Pl D) (d : D.host.F) (hdI : (d : D.host.E) ∈ I)
    (hdI' : ∀ x ∈ I, ∃ y : 𝓞 D.host.E, (y : D.host.E) = (d : D.host.E) * x)
    (hsc : ∀ α ∈ intAf D.host.F, (∀ w, ¬ w = v → evalV D.host.F w α = 0) →
      ∃ α' ∈ intAf D.host.F, (∀ w, ¬ w = v → evalV D.host.F w α' = 0) ∧ α = α' * algebraMap D.host.F (Af D.host.F) d) :
    latO S U LS (idLat I LU : Set _) (· = v) = latO S U LS (LU : Set _) (· = v) := by
  have hAA : ∀ a ∈ D.host.AA, ∀ c : 𝓞 D.host.E, a * (c : D.host.E) ∈ D.host.AA := fun a ha c => by
    have := Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) c ha
    rwa [Algebra.smul_def, mul_comm] at this
  have hgen : ∀ α ∈ intAf D.host.F, (∀ w, ¬ w = v → evalV D.host.F w α = 0) → ∀ a ∈ D.host.AA, ∀ s ∈ LS, ∀ t ∈ LU,
      gen S U α a s t ∈ latO S U LS (LU : Set _) (· = v) := fun α hα hP a ha s hs t ht =>
    AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  refine le_antisymm ((AddSubgroup.closure_le _).2 ?_) ((AddSubgroup.closure_le _).2 ?_)
  · rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    obtain ⟨α', hα', hP', rfl⟩ := hsc α hα hP
    show gen S U (α' * algebraMap D.host.F (Af D.host.F) d) a s t ∈ (latO S U LS (LU : Set _) (· = v) : Set (WO S U))
    rw [SetLike.mem_coe]
    induction ht using Submodule.span_induction generalizing a with
    | mem z hz =>
      obtain ⟨s', hs', y, hy, rfl⟩ := hz
      obtain ⟨yy, hyy⟩ := hdI' s' hs'
      rw [gen_scale, ← hyy]
      exact hgen α' hα' hP' _ (hAA a ha yy) s hs y hy
    | zero =>
      rw [gen_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [gen_add]
      exact add_mem (hx a ha) (hy a ha)
    | smul c x _ hx =>
      rw [gen_smul]
      exact hx _ (hAA a ha c)
  · rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    obtain ⟨α', hα', hP', rfl⟩ := hsc α hα hP
    show gen S U (α' * algebraMap D.host.F (Af D.host.F) d) a s t ∈ (latO S U LS (idLat I LU : Set _) (· = v) : Set (WO S U))
    have e := gen_scale S U α' d a 1 s t
    rw [one_smul, mul_one, mul_comm a] at e
    rw [SetLike.mem_coe, e, mul_comm (d : D.host.E) a, ← gen_smulE]
    exact AddSubgroup.subset_closure ⟨α', hα', hP', a, ha, s, hs, _, Submodule.subset_span ⟨_, hdI, t, ht, rfl⟩, rfl⟩

theorem latO_shiftId {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (v : GlobalTheory.FinPl.Pl D)
    (hv : v ∉ G.pl.S0) (S U : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LU : GlobalTheory.FinPl.Lat U) :
    latO S U LS (idLat (shiftId G) LU : Set _) (· = v) = latO S U LS (LU : Set _) (· = v) := by
  obtain ⟨d, hdv, hdI, hdI'⟩ := GlobalTheory.T.exists_unit_mem_modulusDivConjugateIdeal G v hv
  exact latO_idLat_at S U LS LU _ v (d : D.host.F) hdI hdI' (GlobalTheory.T.integralFiniteAdele_supported_div_prime_to_place D v d hdv)

end GlobalTheory.AscFin.StdOff

open GlobalTheory.AscFin.StdOff GlobalTheory.FinZeta.VacOff

theorem GlobalTheory.AscFin.stdAt_pcBF : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0,
    StdAt (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) v := by
  classical
  intro D _ T L _ _ sc G W _ _ F _ ρ h v hv
  have hoff : ∀ PP ∈ G.pl.W0, PP.under (𝓞 D.host.F) ≠ v := fun PP hPP e => by
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hPP
    exact hv (by rw [← e, G.pl.under_w hu]; exact hu)
  refine ⟨fun a ha => ?_, fun a ha => ?_, fun ξ hξ => ?_⟩
  · have hu := mxAt_mul' ha (F.dB ρ h).pX
    exact depLat_iff_at hoff _ hu
  · refine ⟨idem D (· = v) • a, fun i j => (mem_idOff_iff _ _).2 (by
      rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_sub, ← mul_assoc, idem_mul_self, sub_self]), ?_⟩
    rw [HypDec.extX_apply, Matrix.smul_mul]
    exact idem_mem_latO (latO_negSp_le' _ _ _ _ _ ha.1)
  · have hu := mxAt_mul' (mxAt_mul (F.dJ ρ h).jX hξ) (F.dB ρ h).p0
    show (F.dB ρ h).ext0 _ ((F.dJ ρ h).incX _ ξ) ∈ latBig G (2 * ρ + 1) ↔ _
    exact (mem_latO_at hu).trans (by rw [latO_shiftId G v hv]; exact Iff.rfl)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalCuspidal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ThetaLiftTypeUp

theorem lift_hasTypeAt : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt R.θ (G.P (i + 1)).V τ ((G.P (i + 1)).S τ) (fun h => ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) := by
  intro hL hP D hSz G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i hi Φ hΦ φ hφ hint τ
  have hV : (G.P (i + 1)).V.SigOK := (hG.spaces.P (i + 1) (by omega)).sigOK
  intro C hC δ hδ
  obtain ⟨n, f, p, F, v, hf, hF, happ⟩ := GlobalTheory.T.theta_lift_diagonal_approx_by_fock_lifts hL hP D hSz G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hint C hC (δ / 2) (by linarith)
  have hCA := hL D hSz G₀ Pl0 T A Ks R G hR hG
  choose F' hF' hE using fun l => hCA.up i hi (f l) (hf l) (F l) (hF l)
  have hψ0 : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt R.θ (G.P (i + 1)).V τ ((G.P (i + 1)).S τ)
      (∑ l, F' l (G.ItU i (p l) (v l))) :=
    (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.typeSub R.θ _ τ _).sum_mem fun l _ => GlobalTheory.T.cuspidal_grid_node_type hP R.θ hR.inf _ hV _ (hF' l) _ τ
  obtain ⟨ψ, hψ, hψC⟩ := hψ0 C hC (δ / 2) (by linarith)
  refine ⟨ψ, hψ, fun x hx => ?_⟩
  have h1 := happ x hx
  have h2 := hψC x hx
  have e : (∑ l, ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω x g (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l))) * F l (v l) g ∂(G.mP i).ν) = (∑ l, F' l (G.ItU i (p l) (v l))) x := by
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun l _ => (hE l (p l) (v l) x).2
  rw [e] at h1
  calc _ = ‖((∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω x g Φ) * φ g ∂(G.mP i).ν) - (∑ l, F' l (G.ItU i (p l) (v l))) x) + ((∑ l, F' l (G.ItU i (p l) (v l))) x - ψ x)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ < δ / 2 + δ / 2 := add_lt_add h1 h2
    _ = δ := by ring

end GlobalTheory.ThetaLiftTypeUp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingCellMassEqConstMulLocalCoefficientsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolding_cell_mass_eq_const_mul_local_coefficients : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ)
    (ρ : ∀ j, Measure ((rowGrp ch.G j).subgroupOf (GfC _))) (μ : ∀ j, Measure (GfC (ch.G.V (.grid D.R.m j)))),
    (∀ j ∈ idx D, (ρ j).IsHaarMeasure ∧ (μ j).IsHaarMeasure) → ∀ j ∈ idx D, ∃ c : ℂ, ∀ t Φ β b, IsRep t ch.S.B s β b →
      ∀ M M' : Vol ch.G, M.Is t → IsTermVol t ch.S.toGridChoice Φ β M' → ∀ x : ℝ≥0, M.ν (.top j) = x • M'.ν (.top j) →
        ∀ hb : b j ∈ GfC _, cellWt (ρ j) (μ j) ((latGrp ch.G j).subgroupOf _) ⟨b j, hb⟩ * ((x : ℝ) : ℂ) =
          c * (GlobalTheory.RowWt.colCoef ch t β j : ℂ) := by
  first | exact @GlobalTheory.CellMass.cell_mass | exact GlobalTheory.CellMass.cell_mass | (intros; apply GlobalTheory.CellMass.cell_mass <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingConditionsOfFlatMapWeilActionNeZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFinCond

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem symplO_extX_extY_pairS {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x y : Mx D T.rank ρ) :
    symplO S T (d.extX T x) (d.extY T y) =
      Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * pairS T x y) := by
  have h := d.hO_ext T x 0 0 y 0 0
  simp only [map_zero, zero_add, add_zero, hO_eq_trace S₀, Matrix.mul_zero, trace_zero] at h
  rw [symplO, h, show pairS T (0 : Mx D T.rank ρ) 0 = 0 by simp [pairS], add_zero]

theorem flatS_smul {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ)
    (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (a : ℂ) (Ψ : WO V W → ℂ) :
    flatS dV dW s x y (a • Ψ) = a • flatS dV dW s x y Ψ :=
  GlobalTheory.HandHom.flatAt_smul ψ dV dW _ _ _ _ _ x y a Ψ

theorem exists_mixS_ne {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ)
    (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (F : WO V W → ℂ) (hF : flatS dV dW s x y F ≠ 0) :
    ∃ u : UX D ρ, ∃ w₀, dV.mixS W ψ s.vS.μ s.vS.𝓕 F (x ⬝ u.1.1) w₀ ≠ 0 := by
  by_contra hne
  push_neg at hne
  apply hF
  funext w
  have h0 : ∀ u : UX D ρ, GlobalTheory.MixPer.flatFun ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 x y F w u = 0 := by
    intro u
    have hg : dV.mixS W ψ s.vS.μ s.vS.𝓕 F (x ⬝ u.1.1) = (0 : ℂ) • dV.mixS W ψ s.vS.μ s.vS.𝓕 F (x ⬝ u.1.1) := by
      funext w₀; simp [hne u w₀]
    simp only [GlobalTheory.MixPer.flatFun, GlobalTheory.MixPer.evalAt]
    rw [hg, GlobalTheory.HandHom.mixT_smul, zero_smul]
    simp
  simp only [flatS, GlobalTheory.MixPer.flatAt, h0, integral_zero, Pi.zero_apply]

theorem actO_one_extX {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (h : GA D W) (a : Mx D W.rank ρ) :
    actO V W 1 h (d.extX W a) = d.extX W (mt W h ⬝ a) := by
  simp only [actO, HypDec.extX, AddMonoidHom.coe_mk, ZeroHom.coe_mk, inv_one, mt_one, Matrix.mul_one, Matrix.mul_assoc]

theorem actO_one_extY {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (h : GA D W) (a : Mx D W.rank ρ) :
    actO V W 1 h (d.extY W a) = d.extY W (mt W h ⬝ a) := by
  simp only [actO, HypDec.extY, AddMonoidHom.coe_mk, ZeroHom.coe_mk, inv_one, mt_one, Matrix.mul_one, Matrix.mul_assoc]

theorem weilAction_one_wittExtZero {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (h : GA D W) (a : WO V₀ W) :
    actO V W 1 h (d.ext0 W a) = d.ext0 W (mt W h ⬝ a) := by
  simp only [actO, HypDec.ext0, AddMonoidHom.coe_mk, ZeroHom.coe_mk, inv_one, mt_one, Matrix.mul_one, Matrix.mul_assoc]

theorem eq_one_of_smul {α : Type} {F : α → ℂ} (hF : F ≠ 0) {c c' : ℂ} (h : c • F = c' • F) : c = c' := by
  obtain ⟨w, hw⟩ := Function.ne_iff.1 hF
  have e := congrFun h w
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e hw
  have : (c - c') * F w = 0 := by rw [sub_mul, e, sub_self]
  rcases mul_eq_zero.1 this with h1 | h1
  · exact sub_eq_zero.1 h1
  · exact absurd h1 hw

theorem pairS_sub_left {T : HSp D} {ρ : ℕ} (x x' y : Mx D T.rank ρ) : pairS T (x - x') y = pairS T x y - pairS T x' y := by
  simp only [pairS, Matrix.mul_sub, Matrix.trace_sub]

theorem pairS_idem {T : HSp D} {ρ : ℕ} {c : AE D} (hc : c * c = c) (hcA : cA D c = c) (x y : Mx D T.rank ρ) :
    pairS T (c • x) (c • y) = pairS T x (c • y) := by
  simp only [pairS, adj_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, hcA]
  rw [← mul_assoc, hc]

set_option maxHeartbeats 1000000 in

theorem cond_of_flatS_ne : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (y : Mx D V₀.rank σ), LinearIndependent D.host.E x₀.transpose → ∀ p : Pieces V₀ W W₀ ρ σ, p.Is dV dW (rat x₀) ψ → ∀ Φ ∈ cls dV dW p (rat x₀) y ψ, ∀ h, flatS dV dW s (rat x₀) y (s.om (1, h) Φ) ≠ 0 → Cond dW p (rat x₀) y ψ (fun _ => True) h := by
  intro D ψ V V₀ W W₀ ρ σ dV dW s x₀ y hli p hp Φ hΦ h hne
  obtain ⟨hΦt, hA1, hA2, hB1, -, -⟩ := hΦ
  have hf : IsThetaFunO ψ V W (s.om (1, h) Φ) := s.weil.om_pres _ _ hΦt
  have laws := GlobalTheory.T.flatMap_heisenberg_and_hom_transformation D ψ V V₀ W W₀ ρ σ dV dW s x₀ y hli _ hf
  refine ⟨?_, ?_, ?_⟩
  ·
    obtain ⟨u, w₀, hM⟩ := exists_mixS_ne dV dW s (rat x₀) y _ hne
    obtain ⟨ε, hε⟩ : ∃ ε, ε = GlobalTheory.FinPlLoc.idem D (fun _ => True) := ⟨_, rfl⟩
    have hεε : ε * ε = ε := by rw [hε]; exact GlobalTheory.FinPlLoc.idem_mul_self _
    have hcA : cA D ε = ε := by rw [hε]; exact GlobalTheory.FinPlLoc.cA_idem _
    obtain ⟨A, hAdef⟩ : ∃ A : Mx D W.rank ρ, A = mt W h⁻¹ ⬝ ((rat x₀ : Mx D W.rank ρ) ⬝ u.1.1) := ⟨_, rfl⟩
    have key : ∀ a' ∈ p.A₂, ψ (symplO V W (dV.extX W A) (dV.extY W a')) =
        ψ (symplO V W (dV.extX W (rat x₀)) (dV.extY W a')) := by
      intro a' ha'
      have e1 : heisO ψ V W (dV.extY W (mt W h ⬝ a')) (s.om (1, h) Φ) =
          ψ (symplO V W (dV.extX W (rat x₀)) (dV.extY W a')) • s.om (1, h) Φ := by
        rw [← actO_one_extY, ← s.weil.om_heis 1 h _ Φ hΦt, hA2 a' ha', map_smul]
      have e2 := GlobalTheory.MixModel.Check.mixS_heis_extY dV s.vS.covol hf (mt W h ⬝ a') ((rat x₀ : Mx D W.rank ρ) ⬝ u.1.1) w₀
      rw [e1, GlobalTheory.HandHom.mixS_smul, Pi.smul_apply, smul_eq_mul] at e2
      have e3 : (ψ (symplO V W (dV.extX W (rat x₀)) (dV.extY W a')) -
          ψ (symplO V W (dV.extX W ((rat x₀ : Mx D W.rank ρ) ⬝ u.1.1)) (dV.extY W (mt W h ⬝ a')))) *
          dV.mixS W ψ s.vS.μ s.vS.𝓕 (s.om (1, h) Φ) ((rat x₀ : Mx D W.rank ρ) ⬝ u.1.1) w₀ = 0 := by
        rw [sub_mul, e2, sub_self]
      rcases mul_eq_zero.1 e3 with h1 | h1
      · rw [hAdef, ← GlobalTheory.StripVanish.symplO_extX_extY_mt]; exact (sub_eq_zero.1 h1).symm
      · exact absurd h1 hM
    refine ⟨u, ε • (A - rat x₀), ?_, ?_⟩
    · have hεb : MxAt (fun _ => True) (ε • (A - rat x₀)) := fun i j => by
        rw [GlobalTheory.FinPlLoc.mem_idAt_iff, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← hε, hεε]
      refine (hp.dualA _ hεb).2 fun a' ha' => ?_
      have ha'e : ε • a' = a' := Matrix.ext fun i j => by
        rw [Matrix.smul_apply, smul_eq_mul, hε, ← GlobalTheory.FinPlLoc.mem_idAt_iff]; exact hp.a₂.fin a' ha' i j
      have hsym : symplO V W (dV.extX W (ε • (A - rat x₀))) (dV.extY W a') =
          symplO V W (dV.extX W (A - rat x₀)) (dV.extY W a') := by
        rw [← ha'e, symplO_extX_extY_pairS, symplO_extX_extY_pairS, pairS_idem hεε hcA]
      have hsub : symplO V W (dV.extX W (A - rat x₀)) (dV.extY W a') =
          symplO V W (dV.extX W A) (dV.extY W a') - symplO V W (dV.extX W (rat x₀)) (dV.extY W a') := by
        rw [symplO_extX_extY_pairS, symplO_extX_extY_pairS, symplO_extX_extY_pairS, pairS_sub_left, mul_sub, map_sub]
      rw [hsym, hsub, sub_eq_add_neg, AddChar.map_add_eq_mul, key a' ha', ← AddChar.map_add_eq_mul, add_neg_cancel,
        AddChar.map_zero_eq_one]
    · rw [← hAdef]
      intro i j
      rw [GlobalTheory.FinPlLoc.mem_idOff_iff, ← hε]
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      rw [mul_sub ε (A i j - (rat x₀ : Mx D W.rank ρ) i j), ← mul_assoc, hεε, sub_self]
  ·
    intro N _ hN hA
    have key : heisO ψ V W (dV.extX W ((rat x₀ : Mx D W.rank ρ) ⬝ N)) (s.om (1, h) Φ) = s.om (1, h) Φ := by
      have e : dV.extX W ((rat x₀ : Mx D W.rank ρ) ⬝ N) =
          actO V W 1 h (dV.extX W (mt W h⁻¹ ⬝ ((rat x₀ : Mx D W.rank ρ) ⬝ N))) := by
        rw [actO_one_extX, ← Matrix.mul_assoc, mt_mul_inv, Matrix.one_mul]
      rw [e, ← s.weil.om_heis 1 h _ Φ hΦt, hA1 _ hA]
    have e := laws.1 N hN
    rw [key] at e
    exact eq_one_of_smul hne (e.symm.trans (one_smul ℂ _).symm)
  ·
    intro ξ hξ ξ' _ hξ'
    have key : heisO ψ V W (dV.ext0 W (dW.incX V₀ ξ')) (s.om (1, h) Φ) =
        ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) • s.om (1, h) Φ := by
      have e : dV.ext0 W (dW.incX V₀ ξ') = actO V W 1 h (dV.ext0 W (dW.incX V₀ ξ)) := by
        rw [weilAction_one_wittExtZero, hξ']
      rw [e, ← s.weil.om_heis 1 h _ Φ hΦt, hB1 ξ hξ, map_smul]
    have e := laws.2 ξ'
    rw [key, flatS_smul] at e
    exact (eq_one_of_smul hne e).symm

end GlobalTheory.AscFinCond
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionMovesStandardVacuumTopNodeEqCharSmulStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilAction_moves_standardVacuum_topNode_eq_char_smul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ Tm : (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t (j + 1))) 1 (S.Z.vac (.top t (j + 1))) Tm →
      W.om (.top t (j + 1)) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))), 1) (S.Z.vac (.top t (j + 1))) =
        (∏ w : locPl G t, ((((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)))⁻¹ : ℂˣ) : ℂ)) •
          Tm fun x => halfInd e (stdLatO S (.top t (j + 1))) (actO _ _ (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ 1⁻¹ x) := by
  first | exact @GlobalTheory.TopLevelInv.vac_move_high_eq | exact GlobalTheory.TopLevelInv.vac_move_high_eq | (intros; apply GlobalTheory.TopLevelInv.vac_move_high_eq <;> assumption)
end

