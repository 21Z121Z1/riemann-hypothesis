import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.HermitianForms.TiedBr
import Formalism.LocalToGlobal.HermitianForms.Interlace
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.InterlaceDifferenceShiftInvariant
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0443
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0447
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0449
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0385
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0450
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0451
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0445
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0397
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0453
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0452
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricFrameReducesToBasisModPlace

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastAllTranspose
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option maxHeartbeats 2000000

namespace GlobalTheory.Mem.Col2.LowerTie

section Gen
open Formalism.L2.Forms
variable {ι : Type} [Fintype ι] {N n : ℕ}

theorem lastAll_transpose (a : ι → ℂˣ) (τ : ι) :
    (((lastAll N a τ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ))ᵀ = ((lastAll N a τ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := by
  ext i j
  simp only [Matrix.transpose_apply, lastAll, lastGL_apply]
  by_cases h : i = j
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem fnOf_lastAll (G : ι → Matrix (Fin N) (Fin N) ℂ) (lam : ι → DomWeight N) (a : ι → ℂˣ) (P : Pol ℂ ι N) :
    fnOf G (shiftOf lam) (fun τ => ((lastAll N a τ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) P =
      fnOf G (shiftOf lam) 1 (actP lam (lastAll N a) P) := by
  have h := fnOf_mul G (shiftOf lam) (fun τ => ((lastAll N a τ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) 1 P
  simp only [Pi.one_apply, mul_one] at h
  rw [h]
  refine congrArg (fnOf G (shiftOf lam) 1) ?_
  have e : trAct (lastAll N a) = Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => ((lastAll N a τ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) := by
    unfold trAct
    simp only [lastAll_transpose]
  simp only [actP, detTwK, detPow, shiftOf, LinearMap.smul_apply, AlgHom.toLinearMap_apply, e]
  refine congrArg (· • _) (Finset.prod_congr rfl fun τ _ => ?_)
  rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]

theorem scalar_last (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) (h : ∀ i, 0 ≤ Br.bBr hN lam sg i) (a : ℂˣ) :
    (a : ℂ) ^ (-Br.nBr lam sg) * ((a : ℂ) ^ lam.detShift * ∏ s, (a : ℂ) ^ (Br.bBr hN lam sg s).toNat) = 1 := by
  subst hN
  have ha : (a : ℂ) ≠ 0 := a.ne_zero
  have e : ∏ s, (a : ℂ) ^ (Br.bBr rfl lam sg s).toNat = (a : ℂ) ^ (∑ s, Br.bBr rfl lam sg s) := by
    have : ∀ s, (a : ℂ) ^ (Br.bBr rfl lam sg s).toNat = (a : ℂ) ^ (Br.bBr rfl lam sg s) := fun s => by
      rw [← zpow_natCast, Int.toNat_of_nonneg (h s)]
    simp only [this]
    induction (Finset.univ : Finset (Fin n)) using Finset.cons_induction with
    | empty => simp
    | cons x s hx ih => rw [Finset.prod_cons, Finset.sum_cons, zpow_add₀ ha, ih]
  have e2 : Br.nBr lam sg = lam.detShift + ∑ s, Br.bBr rfl lam sg s := by
    simp only [Br.nBr, Br.bBr, DomWeight.detShift, Finset.sum_sub_distrib, Fin.sum_univ_castSucc]
    simp [Br.iC]
    change ∑ i : Fin n, lam.w i.castSucc + lam.w (Fin.last n) - ∑ i, sg.w i = lam.w (Fin.last n) + (∑ x : Fin n, lam.w x.castSucc - ∑ i, sg.w i)
    ring
  rw [e, ← zpow_add₀ ha, ← zpow_add₀ ha, e2]
  simp

theorem branchingProjection_act_last (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n)
    (h : ∀ τ i, 0 ≤ Br.bBr hN (lam τ) (sg τ) i) (a : ι → ℂˣ) (P : Pol ℂ ι N) :
    (∏ τ, (a τ : ℂ) ^ (-Br.nBr (lam τ) (sg τ))) • (Br.brStdP hN lam sg (actP lam (lastAll N a) P) : Pol ℂ ι n) =
      (Br.brStdP hN lam sg P : Pol ℂ ι n) := by
  rw [branchingProjection_last, smul_smul]
  have e : (∏ τ, (a τ : ℂ) ^ (-Br.nBr (lam τ) (sg τ))) * (detTwK lam (lastAll N a) * ∏ τ, ∏ s, (a τ : ℂ) ^ Br.bExp hN lam sg τ s) = 1 := by
    have h2 : detTwK lam (lastAll N a) = ∏ τ, (a τ : ℂ) ^ (lam τ).detShift := by
      simp only [detTwK, detPow, lastAll, det_lastGL' hN, Units.val_zpow_eq_zpow_val]
    rw [h2, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    exact scalar_last hN (lam τ) (sg τ) (h τ) (a τ)
  rw [e, one_smul]
end Gen
end GlobalTheory.Mem.Col2.LowerTie

namespace GlobalTheory.Mem.Col2.LowerTie

section Rec
variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)

theorem embT_eq : Formalism.L2.Forms.embT (I.rec7 l Z) = embAt B.embLL B.fields.emb := by
  funext τ
  ext y
  show B.host.φ₀ _ = _
  rw [← B.embE_φ₀]
  rfl

include l in
theorem pi_mul_star : ((X.piT u : 𝓞 B.host.E) : B.host.E) * star ((X.piT u : 𝓞 B.host.E) : B.host.E) = (B.T u : B.host.E) := by
  have h := congrArg (fun z : 𝓞 B.fields.E => (z : B.fields.E)) (l.pr.piT_norm u)
  simp only [map_mul, map_natCast] at h
  exact h

include l in
theorem star_pi_ne : star ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 0 := (l.per u I.mu0).tz_ne

theorem bZ_std (hO : I.Ok) (hP : TC.Pins B X) (z0 : Fin (B.R.N B.R.m) → B.host.E)
    (hz : ∀ j, z0 j = if j.1 + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0) :
    bZ (D := I.rec7 l Z) u z0 =
      Matrix.diagonal fun i : Fin (B.R.N B.R.m) => if i.1 + 1 = B.R.N B.R.m then (star ((X.piT u : 𝓞 B.host.E) : B.host.E))⁻¹ else 1 := by
  have hc := (spaces_in_coordinates I hO hP l Z).2.2.1
  have hπ := pi_mul_star I l u
  have h0 := star_pi_ne I l u
  have hp0 : ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 0 := fun h => h0 (by rw [h, star_zero])
  refine Matrix.ext fun (a b : Fin (B.R.N B.R.m)) => ?_
  have ha := a.2
  have hb := b.2
  rw [Matrix.diagonal_apply]
  by_cases h : b.1 < B.R.N B.R.m - 1
  · have e : bZ (D := I.rec7 l Z) u z0 a b = iXc (I.rec7 l Z) (Pi.single ⟨b.1, h⟩ 1) a := by
      exact (dif_pos h).trans (LinearMap.toMatrix'_apply _ _ _)
    refine (e.trans (hc _ a)).trans ?_
    by_cases hab : a = b
    · subst hab
      rw [dif_pos h, if_pos rfl, if_neg (by omega)]
      exact Pi.single_eq_same (M := fun _ : Fin (B.R.N B.R.m - 1) => B.host.E) _ _
    · rw [if_neg hab]
      split_ifs with h2
      · exact Pi.single_eq_of_ne (M := fun _ : Fin (B.R.N B.R.m - 1) => B.host.E) (fun h3 => hab (Fin.ext (Fin.mk.inj_iff.1 h3))) _
      · rfl
  · have e : bZ (D := I.rec7 l Z) u z0 a b = z0 a / (B.T u : B.host.E) := by
      exact dif_neg h
    rw [e, hz, ← hπ]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, if_pos (by omega), if_pos (by omega)]
      field_simp
    · rw [if_neg hab, if_neg (fun h3 => hab (Fin.ext (by omega))), zero_div]

def aT (τ : Tau B.R) : ℂˣ :=
  Units.mk0 (embAt B.embLL B.fields.emb τ (star ((X.piT u : 𝓞 B.host.E) : B.host.E))) ((map_ne_zero _).2 (star_pi_ne I l u))

theorem mZ_std (hO : I.Ok) (hP : TC.Pins B X) (z0 : Fin (B.R.N B.R.m) → B.host.E)
    (hz : ∀ j, z0 j = if j.1 + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0) :
    mZ (D := I.rec7 l Z) u z0 =
      fun τ => ((lastAll (B.R.N B.R.m) (aT I l u) τ : GL (Fin (B.R.N B.R.m)) ℂ) : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) ℂ) := by
  have h0 := star_pi_ne I l u
  have e : (bZ (D := I.rec7 l Z) u z0)⁻¹ =
      Matrix.diagonal fun i : Fin (B.R.N B.R.m) => if i.1 + 1 = B.R.N B.R.m then star ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1 := by
    rw [bZ_std I l Z u hO hP z0 hz]
    refine Matrix.inv_eq_left_inv (A := Matrix.diagonal fun i : Fin (B.R.N B.R.m) =>
      if i.1 + 1 = B.R.N B.R.m then (star ((X.piT u : 𝓞 B.host.E) : B.host.E))⁻¹ else 1) ?_
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    split_ifs
    · exact mul_inv_cancel₀ h0
    · exact mul_one 1
  funext τ
  refine Matrix.ext fun (a b : Fin (B.R.N B.R.m)) => ?_
  have e2 : mZ (D := I.rec7 l Z) u z0 τ a b = embAt B.embLL B.fields.emb τ ((Matrix.diagonal fun i : Fin (B.R.N B.R.m) =>
      if i.1 + 1 = B.R.N B.R.m then star ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1) a b) := by
    unfold mZ
    rw [e, embT_eq]
    rfl
  rw [e2]
  simp only [lastAll, lastGL_apply, Matrix.diagonal_apply]
  split_ifs <;> simp [aT]

end Rec
end GlobalTheory.Mem.Col2.LowerTie

namespace GlobalTheory.Mem.Col2.LowerTie

theorem lowerMap_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
    ∀ (u : B.Word) (Ch : ℕ → Type) (chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i) (F : FormsTiedSym (I.rec7 l Z) u Ch chOf),
    I.StdF l Z u F → ∀ (ψ : ((I.rec7 l Z).mem u).P.Wz) (c : ((I.rec7 l Z).fm u).clsP)
      (P : MvPolynomial ((I.rec7 l Z).what₂.Tau × Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m) × Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m)) ℂ),
      (∀ s, F.eWz ψ c s = fnOf _ (shiftOf (Formalism.L2.Forms.lamT u (I.rec7 l Z).R.m)) (mZ u F.til.z0) P
        ((F.val (I.rec7 l Z).R.m le_rfl (Or.inr rfl)).eY s)) →
      F.valP.eW (((I.rec7 l Z).mem u).P.lowerMap ψ) c =
        fnOf _ (shiftOf (Formalism.L2.Forms.sgT u)) 1 (Formalism.L2.Ker.brTen (I.rec7 l Z) u P) := by
  intro B X I hO hP l Z u Ch chOf F hS ψ c P hψ
  have hl : Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u = B.wts.lamTrue u B.R.m := funext (trueWeight_lastStep_trueColumns I l Z u)
  have hs : Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u = B.wts.sgTrue := funext (trueRowWeight_trueColumns I l Z u)
  have hl' : Formalism.L2.Forms.lamT (D := I.rec7 l Z) u (I.rec7 l Z).R.m = B.wts.lamTrue u B.R.m := hl
  have hs' : Formalism.L2.Forms.sgT (D := I.rec7 l Z) u = B.wts.sgTrue := hs
  have hI : ∀ τ i, 0 ≤ Br.bBr (N_m_succ B.R) (B.wts.lamTrue u B.R.m τ) (B.wts.sgTrue τ) i := by
    intro τ i
    have h := (Formalism.MainNotions.product_first_zeroth_parts.interlaceTr (I.rec7 l Z) u (sg_interlace F.valP) τ i).1
    rw [hl, hs] at h
    exact sub_nonneg.2 h
  have h1 : ψ c = fnOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) 1
      (actP (B.wts.lamTrue u B.R.m) (lastAll (B.R.N B.R.m) (aT I l u)) P) := by
    refine Eq.trans ?_ (fnOf_lastAll (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (B.wts.lamTrue u B.R.m) (aT I l u) P)
    funext s
    have h := hψ s
    rw [hS.eWz, hl', mZ_std I l Z u hO hP _ hS.z0] at h
    refine h.trans ?_
    have h2 := hS.eY B.R.m le_rfl (Or.inr rfl) s
    exact congrArg (fnOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) _ P) (Subtype.ext h2)
  have h3 : polOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) (Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m)) (ψ c) =
      actP (B.wts.lamTrue u B.R.m) (lastAll (B.R.N B.R.m) (aT I l u)) P := by
    have e : (fun τ => ((Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m)).1 τ)⁻¹) = 1 := funext fun τ => inv_one
    have h := polOf_fnOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) (Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m))
      (actP (B.wts.lamTrue u B.R.m) (lastAll (B.R.N B.R.m) (aT I l u)) P)
    rw [e] at h
    rw [h1]
    exact h
  have h4 : Formalism.L2.Ker.brTen (I.rec7 l Z) u P = (Br.brStdP (N_m_succ B.R) (B.wts.lamTrue u B.R.m) B.wts.sgTrue P : Pol ℂ (Tau B.R) (B.R.N B.R.m - 1)) := by
    have h := blk_brOne (ι := Tau B.R) (N_m_succ B.R) (B.wts.lamTrue u B.R.m) B.wts.sgTrue P
    refine Eq.trans ?_ h
    unfold Formalism.L2.Ker.brTen
    rw [hl, hs]
    rfl
  have h5 := branchingProjection_act_last (N_m_succ B.R) (B.wts.lamTrue u B.R.m) B.wts.sgTrue hI (aT I l u) P
  funext s
  rw [hS.eW _ c s ⟨s.1, s.2⟩ rfl, hs', h4, ← h5, ← h3]
  rfl

theorem chi_top_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
    ∀ (u : B.Word) (Ch : ℕ → Type) (chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i) (F : FormsTiedSym (I.rec7 l Z) u Ch chOf),
    I.StdF l Z u F → ∃ n : ℕ, 0 < n ∧ ∀ x : (F.cls (I.rec7 l Z).R.m le_rfl (Or.inr rfl)).lev.U,
      (((F.cls (I.rec7 l Z).R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ) ^ n = 1 ∧
        ∃ r : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL r = (((F.cls (I.rec7 l Z).R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ) :=
  fun {B} {_} I hO hP l Z u _ _ F hS =>
    ChiFinTop.chi_top_root_rat I hO hP l Z u (F.cls B.R.m le_rfl (Or.inr rfl)) (hS.ends B.R.m le_rfl (Or.inr rfl))

end GlobalTheory.Mem.Col2.LowerTie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastThetaStepKeepsFaceLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.DTheta

section TopLevProof

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem liftsExist_top (R : RealDat D A Ks) (hl : R.toLevCh.Is A.μ0) (t : T) (g0 : G0 R.Pg D.R.r) :
    ∃ κ, IsLevelLift D.sp.X' R.βX (R.datXt t) g0 κ := by
  obtain ⟨c, hc⟩ := hl.βX
  exact GlobalTheory.T.parahoricLevel_liftsExist D.sp.X' R.βX (R.datXt t) _ _ hc (GlobalTheory.ChainEquiv.places_sep R.toLevCh _ hl t).1
    (GlobalTheory.ChainEquiv.places_sep R.toLevCh _ hl t).2 g0

set_option maxHeartbeats 2000000 in

theorem topLev_of_clauses (R : RealDat D A Ks) (F : Face D A) (hl : R.toLevCh.Is A.μ0) (hM : R.IsModels) (hc : R.IsChain)
    (hS : ∀ t j, j < D.R.m → SchurMult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv))
      (levChi _ (R.βY j) (R.datYt t j R.triv)) (R.νY t j) (R.fdY t j)) : TopLev R F := by
  intro b t y hy
  have hm : D.R.m - 1 < D.R.m := by have := D.R.two_le_m; omega
  have hrel : ∀ p : (R.levR F b).H, GlobalTheory.ChainEquiv.Rel R t p (D.R.m - 1) (R.ioX t y)
      ((((R.levR F b).chi p : ℂˣ) : ℂ) • R.ioX t y) := by
    intro p
    have hL := liftsExist_top R hl t (p : G0 R.Pg D.R.r)
    refine hL.elim fun κ' hκ' => ?_
    intro κ hκ v g
    have hF : ∀ w h, (((((R.levR F b).chi p : ℂˣ) : ℂ) • y : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) :
        SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) w h =
        (levChi _ R.βX (flagL (R.datXt t)) κ')⁻¹ * (y : SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) w (h * κ') := by
      intro w h
      have hT : HasType D.sp.X' R.βX (withP (R.datXt t) (R.levR F b)) ((y : SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) w) :=
        (GlobalTheory.ChainEquiv.multT_value _ _ _ _ _ hy w).2
      rw [← GlobalTheory.KeepLevel.eigen_of_hasType hT p hκ' h]
      rfl
    have key := GlobalTheory.ChainEquiv.step R.ψ R.θ hM.inf _ _ (R.ωX t) (hc.ωX t) _ _ _ _ (R.vX t) (hc.ptX t) (R.MY (D.R.m - 1))
      (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) rfl _ (GlobalTheory.ChainEquiv.meas_chain hM.νY hM.νY' t _ hm).1 _
      (GlobalTheory.ChainEquiv.meas_chain hM.νY hM.νY' t _ hm).2
      (hS t _ hm) R.ItX (hc.ItX t).ne _ (GlobalTheory.ChainEquiv.range_left R.cX R.prX (R.HX t) _ _ (hM.HX t).2.1) R.βX (R.datXt t) _
      (hM.νX t).1.1 _ (hM.νX t).2 (R.ioX t) (hc.ioX t) (p : G0 R.Pg D.R.r) κ hκ (p : G0 R.Pg D.R.r) κ' hκ' _
      (GlobalTheory.T.lastVector_lift_pair_flagLevel_characters R hl hM.inf hc.ωX hc.vX t (p : G0 R.Pg D.R.r) κ κ' hκ hκ') y _ hF v g
    have e := (R.ioX t).map_smul (((R.levR F b).chi p : ℂˣ) : ℂ) y
    exact (congrArg (fun U : R.CC t (D.R.m - 1) => (U : SmT (R.MY (D.R.m - 1)) →ₗ[ℂ] (GA D (Yc D (D.R.m - 1)) → ℂ)) v g)
      e).symm.trans key
  have hU := (GlobalTheory.KeepLevel.mem_lvlPart_iff (R := R) (R.levR F b) t (D.R.m - 1) (R.ioX t y)).2 hrel
  exact (mem_multT R.θ (R.MY (D.R.m - 1)) _ _ _).2 hU

end TopLevProof

set_option maxHeartbeats 2000000 in

theorem topLev_holds : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → GlobalTheory.Mem.R3.DTheta.TopLev R.toRealDat F.lv2 := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH
  exact topLev_of_clauses R.toRealDat F.lv2 hP.char.base.lev hP.char.base.models
    (RealDat.chain_of_weak hP.char.base.chain hH.aux.ex)
    (fun _ _ _ => GlobalTheory.MultFinite.schurMult hC.2.2.2.2 _ _)

end GlobalTheory.Mem.R3.DTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFrameCharacterMulMovedPoint
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TopCh

theorem toGLm_entry {E : Type} [Field E] {n : ℕ} (f : Sp E n ≃ₗ[E] Sp E n) (i j : Fin n) :
    ((toGLm E n f : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j = f (Pi.single j 1) i := by
  simp [toGLm, Matrix.GeneralLinearGroup.toLin, LinearMap.GeneralLinearGroup.generalLinearEquiv]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
  {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem localComponent_eq_frame {hc : CMData F E} {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) (P : Q) :
    rhoP F P.1 g = Formalism.UG.bc (algebraMap E (P.1.adicCompletion E)) (toGLm E n (p.fr P)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show adAt F P.1 ((g : Matrix (Fin n) (Fin n) (AfE F E)) i j) = algebraMap E _ (((toGLm E n (p.fr P) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j)
  rw [h.fr P i j, toGLm_entry]

theorem rhoT_eq_iota {hc : CMData F E} {k t y x : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : GLG E n SG) (θ : GLQ E n Q)
    (hk : ∀ P : Q, rhoP F P.1 k = 1) (h1 : IsPtOf hc (y * (k * t)) p)
    (h2 : IsPtOf hc (y * x * (k * t)) (((1, h, θ) : UF E n × GLG E n SG × GLQ E n Q) • p)) (P : Q) :
    rhoT F P.1 t x = iotaP P.1 ((θ P)⁻¹) := by
  have e0 : rhoT F P.1 t x = (rhoP F P.1 (y * (k * t)))⁻¹ * rhoP F P.1 (y * x * (k * t)) := by
    rw [← map_inv, ← map_mul, show (y * (k * t))⁻¹ * (y * x * (k * t)) = t⁻¹ * (k⁻¹ * (x * k)) * t by group,
      map_mul, map_mul, map_mul, map_mul, map_inv (rhoP F P.1) k, hk P, inv_one, one_mul, mul_one]
    simp [rhoT]
  rw [e0, localComponent_eq_frame h1 P, localComponent_eq_frame h2 P]
  show _ * Formalism.UG.bc _ (toGLm E n ((1 : Sp E n ≃ₗ[E] Sp E n) * p.fr P * ((θ P)⁻¹).1)) = _
  rw [one_mul, map_mul, map_mul, inv_mul_cancel_left]
  rfl

theorem topChi_eq {K : Type} [Field K] (σ : K →+* ℂ) (U : Subgroup (GL (Fin n) (AfE F E))) (t : GL (Fin n) (AfE F E))
    (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ)
    (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ)))
    (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1)
    (x : topU U t Θ d) (θ : Θ.grp) (hx : ∀ P : Q, rhoT F P.1 t x.1 = iotaP P.1 ((θ.1 P)⁻¹)) :
    topChi σ U t Θ d hd N hdN hΘ x = Units.map (σ : K →* ℂ) (Θ.chr θ) := by
  have hθ : ∀ P : Q, θ.1 P ∈ (Θ P).H := fun P => θ.2 P (Set.mem_univ P)
  have key : ∀ P : Q, locChr P.1 (Θ P) (d P) (hd P) (hdN P) (hΘ P) ⟨rhoT F P.1 t x.1, rhoT_mem x.2 P⟩ =
      ((Θ P).lam ⟨θ.1 P, hθ P⟩)⁻¹ := by
    intro P
    have mem : iotaP P.1 ((θ.1 P)⁻¹) ∈ locLev P.1 (Θ P) (d P) := hx P ▸ rhoT_mem x.2 P
    have e : (⟨rhoT F P.1 t x.1, rhoT_mem x.2 P⟩ : locLev P.1 (Θ P) (d P)) = ⟨iotaP P.1 ((θ.1 P)⁻¹), mem⟩ := Subtype.ext (hx P)
    rw [e, ← map_inv]
    exact qbChr_rat (F := E) P.1 (algebraMap E (P.1.adicCompletion E)) (phi_int P.1) (phi_lt P.1) (Θ P) (d P) (hd P) (hdN P) (hΘ P)
      ((θ.1 P)⁻¹) (inv_mem (hθ P)) mem
  have ec : Θ.chr θ = ∏ P : Q, (Θ P).lam ⟨θ.1 P, hθ P⟩ := by
    unfold LevQFam.chr piChar
    exact MonoidHom.finsetProd_apply (M := ↥(Subgroup.pi Set.univ fun P : Q => (Θ P).H)) _ _ _
  unfold topChi
  rw [MonoidHom.inv_apply, MonoidHom.finsetProd_apply, ec, map_prod, ← _root_.inv_inj, inv_inv, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun P _ => ?_
  show Units.map (σ : K →* ℂ) (locChr P.1 (Θ P) (d P) (hd P) (hdN P) (hΘ P) ⟨rhoT F P.1 t x.1, rhoT_mem x.2 P⟩) = _
  rw [key, map_inv]

theorem chi_eq_of_J0 {K : Type} [Field K] [NeZero n] {hc : CMData F E} (Λ : LevFam E K n SG) (σ : K →+* ℂ)
    {U : Subgroup (GL (Fin n) (AfE F E))} (χ : U →* ℂˣ) {k t : GL (Fin n) (AfE F E)} (ht : t ∈ K1 hc n ST SG)
    (hχ : ∀ (x : U) (z : J0 hc n ST) (h : Λ.grp), z.1 = k⁻¹ * x.1 * k → redG hc n ST SG z = h.1⁻¹ →
      χ x = Units.map (σ : K →* ℂ) (Λ.chr h))
    (x : U) (h : Λ.grp) (hz : (k * t)⁻¹ * x.1 * (k * t) ∈ J0 hc n ST) (hr : redG hc n ST SG ⟨_, hz⟩ = h.1⁻¹) :
    χ x = Units.map (σ : K →* ℂ) (Λ.chr h) := by
  obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.1 ht
  refine hχ x (t' * ⟨_, hz⟩ * t'⁻¹) h ?_ ?_
  · show t'.1 * ((k * t'.1)⁻¹ * x.1 * (k * t'.1)) * t'.1⁻¹ = _
    group
  · rw [map_mul, map_mul, map_inv, MonoidHom.mem_ker.1 ht', hr, one_mul, inv_one, mul_one]

theorem chr_of_J0 {K : Type} [Field K] [NeZero n] (hc : CMData F E) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (d : Q → E)
    (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ)))
    (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1)
    (σ : K →+* ℂ) (U : Subgroup (GL (Fin n) (AfE F E))) (χ : U →* ℂˣ) (k t y : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q)
    (hk : ∀ P : Q, rhoP F P.1 k = 1) (ht : t ∈ K1 hc n ST SG)
    (hχ : ∀ (x : U) (z : J0 hc n ST) (h : Λ.grp), z.1 = k⁻¹ * x.1 * k → redG hc n ST SG z = h.1⁻¹ →
      χ x = Units.map (σ : K →* ℂ) (Λ.chr h))
    (x : topU U t Θ d) (h : Λ.grp) (θ : Θ.grp) (h1 : IsPtOf hc (y * (k * t)) p)
    (h2 : IsPtOf hc (y * x.1 * (k * t)) (((1, h.1, θ.1) : UF E n × GLG E n SG × GLQ E n Q) • p))
    (hz : (k * t)⁻¹ * x.1 * (k * t) ∈ J0 hc n ST) (hr : redG hc n ST SG ⟨_, hz⟩ = h.1⁻¹) :
    χ ⟨x.1, topU_le _ _ _ _ x.2⟩ * topChi σ U t Θ d hd N hdN hΘ x = Units.map (σ : K →* ℂ) (Λ.chr h * Θ.chr θ) := by
  rw [chi_eq_of_J0 Λ σ χ ht hχ ⟨x.1, topU_le _ _ _ _ x.2⟩ h hz hr,
    topChi_eq σ U t Θ d hd N hdN hΘ x θ fun P => rhoT_eq_iota h.1 θ.1 hk h1 h2 P, map_mul]

theorem chi_mul_topChi_moved : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1) (σ : K →+* ℂ) (U : Subgroup (GL (Fin n) (AfE F E))) (χ : U →* ℂˣ) (k t y : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), k ∈ UAd hc n → (∀ P : Q, rhoP F P.1 k = 1) → t ∈ K1 hc n ST SG → (∀ (x : U) (z : J0 hc n ST) (h : Λ.grp), z.1 = k⁻¹ * x.1 * k → redG hc n ST SG z = h.1⁻¹ → χ x = Units.map (σ : K →* ℂ) (Λ.chr h)) → ∀ (x : topU U t Θ d) (h : Λ.grp) (θ : Θ.grp), IsPtOf hc (y * (k * t)) p → IsPtOf hc (y * x.1 * (k * t)) (((1, h.1, θ.1) : UF E n × GLG E n SG × GLQ E n Q) • p) → χ ⟨x.1, topU_le _ _ _ _ x.2⟩ * topChi σ U t Θ d hd N hdN hΘ x = Units.map (σ : K →* ℂ) (Λ.chr h * Θ.chr θ) := by
  intro F E K _ _ _ _ _ _ _ hc n _ ST SG Q Λ Θ d hd N hdN hΘ σ U χ k t y p _ hk ht hχ x h θ h1 h2
  have e : y * (k * t) * ((k * t)⁻¹ * x.1 * (k * t)) = y * x.1 * (k * t) := by group
  obtain ⟨hz, hr⟩ := ((isPtOf_mul_J0 F E hc n ST SG Q (y * (k * t)) ((k * t)⁻¹ * x.1 * (k * t)) p
    (((1, h.1, θ.1) : UF E n × GLG E n SG × GLQ E n Q) • p) h.1).1 h1 (e ▸ h2)).2 rfl
  exact chr_of_J0 hc Λ Θ d hd N hdN hΘ σ U χ k t y p hk ht hχ x h θ h1 h2 hz hr

end GlobalTheory.Mem.Col2.TopCh

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatrixModPlaceBasisChangeEqConjStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixModPlace_basisChange_eq_conj : ∀ (D : D7) (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd) (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E), FixRed X red b → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (P : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) (u : Fin D.R.r → VA X.B.I), (∀ j, u j - ∑ i, ((((((P : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) i j).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • incl X.B.I (b kv i) ∈ wLf X (D.naut.plGw kv.1 kv.2)) → ∀ k ∈ X.B.I.Kset, GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) u k ((((P⁻¹ * red k kv * P) : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) := by
  first | exact @GlobalTheory.Mem.SymFrame.isMatIn_basisChange | exact GlobalTheory.Mem.SymFrame.isMatIn_basisChange | (intros; apply GlobalTheory.Mem.SymFrame.isMatIn_basisChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemGlintOfEntries
section
namespace GlobalTheory.MemGlintOfEntries

theorem mem_glint_of_entries {K : Type} [inst : Field K] {n : ℕ} (O : Subring K)
    (g : GL (Fin n) K)
    (h : ∀ (i j : Fin n), (↑g : Matrix (Fin n) (Fin n) K) i j ∈ O)
    (h' : ∀ (i j : Fin n), (↑g⁻¹ : Matrix (Fin n) (Fin n) K) i j ∈ O) :
    g ∈ Formalism.UG.GLint (Fin n) O := by
  let A : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨_, h i j⟩
  let B : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨_, h' i j⟩
  have hA : O.subtype.mapMatrix A = (↑g : Matrix (Fin n) (Fin n) K) := by
    ext i j; rfl
  have hB : O.subtype.mapMatrix B = (↑g⁻¹ : Matrix (Fin n) (Fin n) K) := by
    ext i j; rfl
  have hinj : Function.Injective
      (O.subtype.mapMatrix : Matrix (Fin n) (Fin n) O → Matrix (Fin n) (Fin n) K) := by
    intro X Y hXY
    ext i j
    exact congrFun (congrFun hXY i) j
  have hAB : A * B = 1 := by
    apply hinj
    rw [map_mul, map_one, hA, hB]
    exact Units.mul_inv g
  have hBA : B * A = 1 := by
    apply hinj
    rw [map_mul, map_one, hA, hB]
    exact Units.inv_mul g
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  apply Units.ext
  ext i j
  rfl

end GlobalTheory.MemGlintOfEntries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormOneIntegralIffConjugateValuationsEqStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_normOneIntegral_iff_conjugate_valuations_eq : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) (a : GlobalTheory.Mem.Chr.Ideles H.E), IsDetLift (host_cmData R H) x.1 a → ((x.1 ∈ Formalism.L2.Herm.IntegralUnitGroup (host_cmData R H)) ↔ ∀ w : HeightOneSpectrum (𝓞 H.E), Valued.v (compAt w a) = Valued.v (compAt (conjPrime₂ w) a)) := by
  first | exact @GlobalTheory.Mem.Col2.FullDt.mem_u1int_iff_val | exact GlobalTheory.Mem.Col2.FullDt.mem_u1int_iff_val | (intros; apply GlobalTheory.Mem.Col2.FullDt.mem_u1int_iff_val <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberLevelPrimeNotMemUnderLevelPrimesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memberLevelPrime_not_mem_under_levelPrimes : ∀ (B : Base) (X : PreX B.toPre) (I : ColIn B X), I.Ok → ∀ (u : B.Word) (P : HeightOneSpectrum (𝓞 B.host.E)), P ∈ uSG (B.primes X).vGs I.SQ → (B.T u : 𝓞 B.host.F) ∉ (P.under (𝓞 B.host.F)).asIdeal := by
  first | exact @GlobalTheory.Mem.LevTwist.T_notMem_under_uSG | exact GlobalTheory.Mem.LevTwist.T_notMem_under_uSG | (intros; apply GlobalTheory.Mem.LevTwist.T_notMem_under_uSG <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointDeterminantEqNormOneClassOfLevelStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointDeterminant_eq_normOneClass_of_level : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (n : ℕ) (ST SG Q SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (p : DecoF H.E n ST SG Q) (y k : GL (Fin n) (AfE H.F H.E)) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)), LevOk H SG SQ → IsPtOf (host_cmData R H) (y * k) (extTo SQ p) → k ∈ Formalism.L2.Herm.UstdAf (host_cmData R H) n → Formalism.L2.Herm.Carries k (stdLat H.E n) (stdLat H.E n) → (∀ P ∈ uSG SG SQ, Formalism.UG.bc (Formalism.UG.prV (E := H.E) (P.under (𝓞 H.F))) k = 1) → Matrix.GeneralLinearGroup.det x.1 = Matrix.GeneralLinearGroup.det y → detPt H SQ p = u1Dt H SQ x := by
  first | exact @GlobalTheory.Mem.Col2.FullDt.detPt_eq_u1Dt_of_level | exact GlobalTheory.Mem.Col2.FullDt.detPt_eq_u1Dt_of_level | (intros; apply GlobalTheory.Mem.Col2.FullDt.detPt_eq_u1Dt_of_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointLatticeIffBaseLatticeDecoratedStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointLattice_iff_baseLattice_decorated : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (S : Submodule (𝓞 E) (Fin n → E)) (k t y : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), t ∈ K1 hc n ST SG → (∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S ↔ (k⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) → IsPtOf hc (y * (k * t)) p → ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) p.deco.1.L ↔ (y⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S := by
  first | exact @GlobalTheory.Mem.Col2.PtLat.latS_deco_iff | exact GlobalTheory.Mem.Col2.PtLat.latS_deco_iff | (intros; apply GlobalTheory.Mem.Col2.PtLat.latS_deco_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricFrameReducesToBasisModPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricFrame_reduces_to_basis_mod_place : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E), (∀ kv : (Σ k : Fin 2, D.nd.PlG k), IsRedBasis X (D.naut.plGw kv.1 kv.2) (b kv)) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ π : Equiv.Perm (Fin D.R.r), ∃ P : G0g D.nd, ∀ (kv : (Σ k : Fin 2, D.nd.PlG k)) (j : Fin D.R.r), GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) (π.symm j) - ∑ i, ((((((P kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) i j).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • incl X.B.I (b kv i) ∈ wLf X (D.naut.plGw kv.1 kv.2) := by
  first | exact @GlobalTheory.Mem.SymFrameRed.symVec_red | exact GlobalTheory.Mem.SymFrameRed.symVec_red | (intros; apply GlobalTheory.Mem.SymFrameRed.symVec_red <;> assumption)
end

