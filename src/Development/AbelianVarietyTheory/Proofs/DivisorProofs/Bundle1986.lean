import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1974
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1699
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1977
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1762
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1773
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0081
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1978
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1445
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1746

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelParabolicConjInvTranspose
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SiegelTransposeInverse

open GlobalTheory.Doubling

theorem conj_mulVec_diag {A n ι : Type} [CommRing A] [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι]
    (e : n ⊕ n ≃ ι) (c : A →+* A) {G t : Matrix n n A} (hG : IsUnit G.det) {p : Matrix (n ⊕ n) (n ⊕ n) A}
    (hp : p * Matrix.fromRows (1 : Matrix n n A) 1 = Matrix.fromRows (1 : Matrix n n A) 1 * t)
    {X Q : Matrix ι ι A} (hQ : p.submatrix e.symm e.symm * Q = 1) (hXQ : X = Qᵀ)
    (hX : Formalism.UG.cT c X * blkMat e G (-G) * X = blkMat e G (-G)) (u : n → A) :
    (blkMat e (1 : Matrix n n A) (-1) * X * blkMat e (1 : Matrix n n A) (-1)) *ᵥ pairVec e u u =
      pairVec e ((G⁻¹ * t.map c * G) *ᵥ u) ((G⁻¹ * t.map c * G) *ᵥ u) := by
  have h1 : blkMat e G (-G) * X = (p.submatrix e.symm e.symm).map c * blkMat e G (-G) := by
    have h0 : Formalism.UG.cT c X = Q.map c := by rw [hXQ]; rfl
    have h2 : (p.submatrix e.symm e.symm).map c * Q.map c = 1 := by
      rw [← Matrix.map_mul, hQ, Matrix.map_one _ (map_zero c) (map_one c)]
    conv_rhs => rw [← hX, h0, Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have h3 : ∀ y : n → A, (p.submatrix e.symm e.symm).map c *ᵥ pairVec e y y =
      pairVec e (t.map c *ᵥ y) (t.map c *ᵥ y) := by
    intro y
    have h4 := congrArg (fun M : Matrix (n ⊕ n) n A => M *ᵥ y)
      ((Matrix.map_mul (f := c) (L := p) (M := Matrix.fromRows (1 : Matrix n n A) 1)).symm.trans
        ((congrArg (fun M : Matrix (n ⊕ n) n A => M.map c) hp).trans Matrix.map_mul))
    simp only [Matrix.fromRows_map, Matrix.map_one _ (map_zero c) (map_one c), ← Matrix.mulVec_mulVec,
      Matrix.fromRows_mulVec, Matrix.one_mulVec] at h4
    rw [← Matrix.submatrix_map, Matrix.submatrix_mulVec_equiv, pairVec, pairVec, ← h4]
    have h7 : (Sum.elim y y ∘ ⇑e.symm) ∘ ⇑e.symm.symm = Sum.elim y y := by
      funext j; simp
    rw [h7]
  have h5 : blkMat e G⁻¹ (-G⁻¹) * blkMat e G (-G) = 1 := by
    rw [blkMat_mul, neg_mul_neg, Matrix.nonsing_inv_mul _ hG, blkMat_one]
  have h6 : X = blkMat e G⁻¹ (-G⁻¹) * ((p.submatrix e.symm e.symm).map c * blkMat e G (-G)) := by
    rw [← h1, ← Matrix.mul_assoc, h5, Matrix.one_mul]
  rw [h6]
  simp only [← Matrix.mulVec_mulVec, blkMat_mulVec, Matrix.neg_mulVec, Matrix.mulVec_neg, Matrix.one_mulVec, neg_neg, h3]

theorem keepsDiag_and_det {A n ι : Type} [CommRing A] [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι]
    (e : n ⊕ n ≃ ι) (c : A →+* A) {G t : Matrix n n A} (hG : IsUnit G.det) {Y : Matrix ι ι A}
    (hY : ∀ u, Y *ᵥ pairVec e u u = pairVec e ((G⁻¹ * t.map c * G) *ᵥ u) ((G⁻¹ * t.map c * G) *ᵥ u)) :
    KeepsDiag e Y ∧ (leviMat e Y).det = c t.det := by
  have hK : KeepsDiag e Y := keepsDiag_of_mulVec fun w hw => by
    obtain ⟨x, rfl⟩ := (mem_diagSub e).1 hw
    rw [hY]
    exact (pairVec_mem_diagSub e).2 rfl
  refine ⟨hK, ?_⟩
  have hL : leviMat e Y = G⁻¹ * t.map c * G := by
    refine Matrix.ext_of_mulVec_single fun j => ?_
    have h := (hK.mulVec_diag (Pi.single j 1)).symm.trans (hY _)
    funext i
    simpa only [pairVec_inl] using congrFun h (e (.inl i))
  rw [hL, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, Matrix.nonsing_inv_mul _ hG,
    Matrix.det_one, one_mul, RingHom.map_det, RingHom.mapMatrix_apply]

open GlobalTheory.DiagThetaRule in
theorem epsD_mul_self {D : D7} (S : HSp D) : epsD S * epsD S = 1 := by
  apply Subtype.ext
  apply Units.ext
  show Formalism.L2.Theta.mt (dblSp S) (epsD S) * Formalism.L2.Theta.mt (dblSp S) (epsD S) = 1
  rw [mt_epsD, blkMat_mul, neg_mul_neg, Matrix.one_mul, blkMat_one]

open GlobalTheory.DiagThetaRule in

theorem exists_siegel_conj (D : D7) (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (p : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB)))
    (t : GL (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E))
    (hp : p.1.1 * GlobalTheory.WeilM.diagCols (Fin S.rank) = GlobalTheory.WeilM.diagCols (Fin S.rank) * t.1)
    (g : GA D (GlobalTheory.Doubling.dblSp S)) (hg : Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp S) g =
      ((GlobalTheory.DblSchr.reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (GlobalTheory.DblSchr.incM_JBd S JB) p)⁻¹).1.1ᵀ) :
    ∃ h : GlobalTheory.Doubling.siegel S, GlobalTheory.DiagThetaRule.epsD S * g = (h : GA D (GlobalTheory.Doubling.dblSp S)) * GlobalTheory.DiagThetaRule.epsD S ∧
      GlobalTheory.Doubling.aP S h = GlobalTheory.Doubling.conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det t) := by
  have hG : IsUnit (JR (F := D.host.F) (AF D.host.F) S.gram).det := by
    have h := ((isHermND_gram S).2.isUnit).map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F))
    rw [RingHom.map_det, RingHom.mapMatrix_apply] at h
    exact h
  have hX : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (Formalism.L2.Theta.mt (dblSp S) g) *
      blkMat finSumFinEquiv (JR (F := D.host.F) (AF D.host.F) S.gram) (-(JR (F := D.host.F) (AF D.host.F) S.gram)) *
      Formalism.L2.Theta.mt (dblSp S) g =
      blkMat finSumFinEquiv (JR (F := D.host.F) (AF D.host.F) S.gram) (-(JR (F := D.host.F) (AF D.host.F) S.gram)) := by
    rw [← JR_dblSp_gram]
    exact g.2
  have hQ : p.1.1.submatrix finSumFinEquiv.symm finSumFinEquiv.symm *
      ((GlobalTheory.DblSchr.reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (GlobalTheory.DblSchr.incM_JBd S JB) p)⁻¹).1.1 = 1 := by
    rw [← GlobalTheory.DblSchr.reG_val (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (GlobalTheory.DblSchr.incM_JBd S JB) p]
    exact Units.mul_inv _
  have hY := keepsDiag_and_det finSumFinEquiv (sigR (AF D.host.F) D.sp.cm.sig) hG
    (conj_mulVec_diag finSumFinEquiv (sigR (AF D.host.F) D.sp.cm.sig) hG hp hQ hg hX)
  refine ⟨⟨epsD S * g * epsD S, mem_siegelOf.2 hY.1⟩, ?_, Units.ext hY.2⟩
  show epsD S * g = epsD S * g * epsD S * epsD S
  rw [mul_assoc, epsD_mul_self, mul_one]

end GlobalTheory.SiegelTransposeInverse
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryInvTransposeOfScaledInverseGram
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SiegelThetaInvT

private theorem invTranspose_abstract {E A n : Type} [Field E] [CommRing A] [Fintype n] [DecidableEq n]
    (ι : E →+* A) (c : A →+* A) (G J : Matrix n n E) (hG : G.det ≠ 0) (x : E) (hx : x ≠ 0) (ξ : A)
    (hξ : ξ • J.map ι = (x • G⁻¹).map ι) (M N : Matrix n n A) (hMN : M * N = 1) (hNM : N * M = 1)
    (hb : Mᵀ * J.map ι * M.map c = J.map ι) :
    (Nᵀ.map c)ᵀ * G.map ι * Nᵀ = G.map ι := by
  have hdet : IsUnit G.det := isUnit_iff_ne_zero.2 hG
  have hKG : G⁻¹.map ι * G.map ι = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hGK : G.map ι * G⁻¹.map ι = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hsm : (x • G⁻¹).map ι = ι x • G⁻¹.map ι := by
    ext i j
    simp [smul_eq_mul, map_mul]
  have hd : ι x⁻¹ * ι x = 1 := by rw [← map_mul, inv_mul_cancel₀ hx, map_one]
  generalize G⁻¹.map ι = K at hKG hGK hsm
  generalize G.map ι = G' at hKG hGK ⊢
  have h1 : ι x • (Mᵀ * K * M.map c) = ι x • K := by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← hsm, ← hξ, Matrix.mul_smul, Matrix.smul_mul, hb]
  have h2 : Mᵀ * K * M.map c = K := by
    have := congrArg (fun X => ι x⁻¹ • X) h1
    simpa only [smul_smul, hd, one_smul] using this
  have hcNM : N.map c * M.map c = 1 := by
    rw [← Matrix.map_mul, hNM]
    exact Matrix.map_one _ (map_zero c) (map_one c)
  have hX : N.map c * G' * Nᵀ * K = 1 := by
    calc N.map c * G' * Nᵀ * K = N.map c * G' * Nᵀ * (Mᵀ * K * M.map c) := by rw [h2]
      _ = N.map c * G' * ((M * N)ᵀ * K) * M.map c := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = N.map c * M.map c := by
          rw [hMN, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_assoc (N.map c), hGK, Matrix.mul_one]
      _ = 1 := hcNM
  have hT : (Nᵀ.map c)ᵀ = N.map c := rfl
  rw [hT]
  calc N.map c * G' * Nᵀ = N.map c * G' * Nᵀ * (K * G') := by rw [hKG, Matrix.mul_one]
    _ = G' := by rw [← Matrix.mul_assoc, hX, Matrix.one_mul]

private def invT {A n : Type} [CommRing A] [Fintype n] [DecidableEq n] (m : GL n A) : GL n A :=
  ⟨(m⁻¹).1ᵀ, m.1ᵀ, by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩

private theorem sigR_eq_cA {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) (x : AF F ⊗[F] E) : sigR (AF F) σ x = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

private theorem invT_mem_HR {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {r : ℕ}
    (G J : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (x : E) (hx : x ≠ 0) (ξ : AF F ⊗[F] E)
    (hξ : ξ • incM F J = incM F (x • G⁻¹))
    (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (incM F J)) :
    ∃ g : HR (AF F) σ G, g.1.1 = (b⁻¹).1.1ᵀ := by
  obtain ⟨m, hm⟩ := b
  have hb : m.1ᵀ * incM F J * m.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) = incM F J := hm
  have hc : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ : AF F ⊗[F] E → AF F ⊗[F] E) = sigR (AF F) σ :=
    funext fun y => (sigR_eq_cA σ y).symm
  rw [hc] at hb
  have key := invTranspose_abstract (inclR (F := F) (AF F)) (sigR (AF F) σ) G J hG x hx ξ hξ m.1 (m⁻¹).1
    (Units.mul_inv m) (Units.inv_mul m) hb
  exact ⟨⟨invT m, key⟩, rfl⟩

theorem _root_.GlobalTheory.T.exists_unitary_invTranspose_of_scaledInverseGram : ∀ (D : D7) (V : HSp D) (J : Matrix (Fin V.rank) (Fin V.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E), ξ • incM D.host.F J = incM D.host.F (D.host.xi0 • V.gram⁻¹) →
    ∀ b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F J),
      ∃ g : GA D V, Formalism.L2.Theta.mt V g = (b⁻¹).1.1ᵀ := by
  intro D V J ξ hξ b
  obtain ⟨g, hg⟩ := invT_mem_HR D.sp.cm.sig V.gram J (GlobalTheory.Doubling.isHermND_gram V).2 D.host.xi0
    (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D) ξ hξ b
  exact ⟨g, hg⟩

end GlobalTheory.SiegelThetaInvT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridRowLevelZeroInfUnitaryEqDatumLevel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.FunObj

variable {D : D7}

def LocCond (w : Pl D.host.E) (inPg inQ : Prop) (r t : ℕ) {m : ℕ} (g : GL (Fin m) (Kw w)) : Prop :=
  g ∈ KO (Kw w) (Fin m) ∧
    (inPg → (∀ a b : Fin m, Formalism.L2.DIV.blkOf r t b < Formalism.L2.DIV.blkOf r t a → valuation (Kw w) (g.1 a b) < 1) ∧
      ∀ a b : Fin m, a.val < r → b.val < r → valuation (Kw w) ((g.1 - 1) a b) < 1) ∧
    (inQ → ∀ a b : Fin m, Formalism.L2.DIV.blk2 r b < Formalism.L2.DIV.blk2 r a → valuation (Kw w) (g.1 a b) < 1)

theorem inBasis_mem_iff {n m : ℕ} (hm : m = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E)
    (K : Subgroup (GL (Fin m) (Kw w))) (p q : Prop) (r t : ℕ) (hK : ∀ g, g ∈ K ↔ LocCond w p q r t g) :
    inBasis hm β w x ∈ K ↔ LocCond w p q r t (inBasis rfl β w x) := by
  subst hm; exact hK _

theorem upperLeftBlock_eq_one_iff_of_mem_blockTri {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (g : GL (Fin n) κ)
    (hg : g ∈ blockTri (blk2 r)) :
    upperLeftBlock hr g = 1 ↔ ∀ a b : Fin n, a.val < r → b.val < r →
      (g : Matrix (Fin n) (Fin n) κ) a b = (1 : Matrix (Fin n) (Fin n) κ) a b := by
  unfold upperLeftBlock
  rw [extendOne_of_mem _ hg]
  constructor
  · intro h a b ha hb
    have e := congrArg (fun u : GL (Fin r) κ => (u : Matrix (Fin r) (Fin r) κ) ⟨a.val, ha⟩ ⟨b.val, hb⟩) h
    have e2 : (g : Matrix (Fin n) (Fin n) κ) a b = (1 : Matrix (Fin r) (Fin r) κ) ⟨a.val, ha⟩ ⟨b.val, hb⟩ := e
    rw [e2, Matrix.one_apply, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg hab, if_neg (fun h' => hab (Fin.ext (Fin.mk.inj h')))]
  · intro h
    apply Units.ext
    ext i j
    have e := h (Fin.castLE hr i) (Fin.castLE hr j) i.2 j.2
    show (g : Matrix (Fin n) (Fin n) κ) (Fin.castLE hr i) (Fin.castLE hr j) = (1 : Matrix (Fin r) (Fin r) κ) i j
    rw [e, Matrix.one_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij, if_neg (fun h' => hij (Fin.castLE_injective hr h'))]

theorem levelChainTypePlaces_subset_chosenPlaces {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T) :
    L.Pg ⊆ G.pl.W0 := by
  classical
  intro PP hP
  obtain ⟨k, hk⟩ := (hL.Pg PP).1 hP
  have hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := L.C.P.overP hk
  have hv : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (PP.under (𝓞 D.host.F)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ PP.asIdeal
    simpa using hg
  have hS : PP.under (𝓞 D.host.F) ∈ G.pl.S0 := by
    refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((GlobalTheory.ChiGrid.S1_mem_OmF D).2 ?_))
    fin_cases k
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
  have hw : G.pl.w (PP.under (𝓞 D.host.F)) ∈ L.Pg := G.pl.w_g _ k hv
  have he : (G.pl.w (PP.under (𝓞 D.host.F))).under (𝓞 D.host.F) = PP.under (𝓞 D.host.F) := G.pl.under_w hS
  rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq he with e | e
  · rw [← e]; exact Finset.mem_image_of_mem _ hS
  · exact absurd (GlobalTheory.GoodPrimes.isConjPl_iff.2 e) ((GlobalTheory.StepLifts.places_apart L hL t).1 PP hP _ (Or.inl hw))

theorem prodLev_inf_UA {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : Lev.IsBaseFrame V β Λ 1) (P : Finset (Pl D.host.E)) {n' : P → ℕ} (hn : ∀ w, n' w = V.rank)
    (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1))) (Ld : LevDat D.host.E ℂ V.rank) (hH : Ld.P.H = ⊥)
    (hPg : Ld.Pg ⊆ P) (hQ : Ld.Q ⊆ P)
    (hK : ∀ w : P, ∀ g, g ∈ K w ↔ LocCond w.1 (w.1 ∈ Ld.Pg) (w.1 ∈ Ld.Q) Ld.r Ld.t g) :
    prodLev β P hn K ⊓ UA D.sp.cm V.gram = lev D.sp.cm V.gram β Ld := by
  have hloc : ∀ (w : P) x, inBasis (hn w) β w.1 x ∈ K w ↔
      LocCond w.1 (w.1 ∈ Ld.Pg) (w.1 ∈ Ld.Q) Ld.r Ld.t (inBasis rfl β w.1 x) :=
    fun w x => inBasis_mem_iff (hn w) β x w.1 (K w) _ _ _ _ (hK w)
  have red0 : ∀ x ∈ St β, ∀ PP (i j : Fin V.rank),
      ((redFn β PP x : GL (Fin V.rank) (kP PP)) : Matrix (Fin V.rank) (Fin V.rank) (kP PP)) i j = 0 ↔
        valuation (Kw PP) ((inBasis rfl β PP x).1 i j) < 1 := by
    intro x hx PP i j
    have e := GlobalTheory.T.latticeStabilizer_reduction_eq_local_reduction β x PP hx i j 0
    simpa using e
  have red1 : ∀ x ∈ St β, ∀ PP (i j : Fin V.rank),
      ((redFn β PP x : GL (Fin V.rank) (kP PP)) : Matrix (Fin V.rank) (Fin V.rank) (kP PP)) i j =
          (1 : Matrix (Fin V.rank) (Fin V.rank) (kP PP)) i j ↔
        valuation (Kw PP) (((inBasis rfl β PP x).1 - 1) i j) < 1 := by
    intro x hx PP i j
    by_cases hij : i = j
    · subst hij
      have e := GlobalTheory.T.latticeStabilizer_reduction_eq_local_reduction β x PP hx i i 1
      simpa [Matrix.one_apply] using e
    · have e := GlobalTheory.T.latticeStabilizer_reduction_eq_local_reduction β x PP hx i j 0
      simpa [Matrix.one_apply, hij] using e
  ext x
  constructor
  · rintro ⟨hx, hU⟩
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hx
    have hA : ∀ w : P, LocCond w.1 (w.1 ∈ Ld.Pg) (w.1 ∈ Ld.Q) Ld.r Ld.t (inBasis rfl β w.1 x) :=
      fun w => (hloc w x).1 (Subgroup.mem_iInf.1 h1 w)
    have hSt : x ∈ St β := GlobalTheory.T.mem_latticeStabilizer_of_local_integral_inBasis β x fun w => by
      by_cases hw : ∃ w0 ∈ P, w.under (𝓞 D.host.F) = w0.under (𝓞 D.host.F)
      · obtain ⟨w0, hw0, e⟩ := hw
        have hK0 := (hA ⟨w0, hw0⟩).1
        rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e with rfl | rfl
        · exact hK0
        · exact GlobalTheory.T.integralGL_conjPlace_of_selfDual_baseFrame V β Λ hβ x hU w0 hK0
      · push_neg at hw
        exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h2 w) hw
    have hgP : ∀ PP ∈ Ld.Pg, redFn β PP x ∈ blockTri (blkOf Ld.r Ld.t) := fun PP hP => by
      rw [mem_blockTri]
      intro a b hab
      exact (red0 x hSt PP a b).2 (((hA ⟨PP, hPg hP⟩).2.1 hP).1 a b hab)
    refine mem_lev.2 ⟨mem_parLev.2 ⟨hU, hSt, hgP, fun PP hP => ?_⟩, ?_⟩
    · rw [mem_blockTri]
      intro a b hab
      exact (red0 x hSt PP a b).2 ((hA ⟨PP, hQ hP⟩).2.2 hP a b hab)
    · rw [hH, Subgroup.mem_bot]
      funext PP
      show upperLeftBlock Ld.hr (redFn β PP.1 x) = 1
      rw [upperLeftBlock_eq_one_iff_of_mem_blockTri _ _ (blockTri_blkOf_le _ _ (hgP PP.1 PP.2))]
      intro a b ha hb
      exact (red1 x hSt PP.1 a b).2 (((hA ⟨PP.1, hPg PP.2⟩).2.1 PP.2).2 a b ha hb)
  · intro hx
    obtain ⟨hpar, hr⟩ := mem_lev.1 hx
    obtain ⟨hU, hSt, hg, hq⟩ := mem_parLev.1 hpar
    refine ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => (hloc w x).2 ⟨inBasis_mem_KO β x hSt w.1, fun hw => ⟨?_, ?_⟩,
      fun hw a b hab => (red0 x hSt w.1 a b).1 (mem_blockTri.1 (hq w.1 hw) a b hab)⟩,
      Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun _ => inBasis_mem_KO β x hSt w'⟩, hU⟩
    · intro a b hab
      exact (red0 x hSt w.1 a b).1 (mem_blockTri.1 (hg w.1 hw) a b hab)
    · intro a b ha hb
      rw [hH, Subgroup.mem_bot] at hr
      have e : upperLeftBlock Ld.hr (redFn β w.1 x) = 1 := congrFun hr ⟨w.1, hw⟩
      rw [upperLeftBlock_eq_one_iff_of_mem_blockTri _ _ (blockTri_blkOf_le _ _ (hg w.1 hw))] at e
      exact (red1 x hSt w.1 a b).1 (e a b ha hb)

theorem givenLevel_zero_iff {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E) (k : ℕ)
    (hk : 1 ≤ k) (g : GL (Fin ((locGrid G t w).rank (0, k))) (Kw w)) :
    g ∈ givenLevel G t w (0, k) ↔ g ∈ (stepGroup L t w k).map (reGL (ixFin G t w k)).toMonoidHom := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact Iff.rfl

theorem levRow_zero_eq_lev : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {U : Set T}
    (S : GridChoice W U) {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (h : 0 ≤ D.R.m),
    HEq (S.levRow t 0 h ⊓ UA D.sp.cm (G.V (.grid 0 D.R.m)).gram) (lev D.sp.cm D.sp.X'.gram L.βX (L.datXt t)) := by
  intro D T L sc G W U S μ₀ hL t h
  classical
  have hr : D.R.r ≤ (G.V (.grid 0 D.R.m)).rank := by rw [← rank_zero_m G]; exact r_le_X
  have hbase : Lev.IsBaseFrame (G.V (.grid 0 D.R.m)) (S.B.β 0 D.R.m) (G.Λ (.grid 0 D.R.m)) 1 := by
    obtain ⟨c, hc⟩ := hL.βX
    rw [one_pow] at hc
    have key : ∀ (X Y : LSp D) (a : GL (Fin X.sp.rank) (Lev.EAf D)) (b : GL (Fin Y.sp.rank) (Lev.EAf D)),
        X = Y → HEq a b → Lev.IsBaseFrame Y.sp b Y.lat 1 → Lev.IsBaseFrame X.sp a X.lat 1 := by
      rintro X _ a b rfl hab h'
      rwa [eq_of_heq hab]
    exact key _ ⟨D.sp.X', L.ΛX⟩ _ _ (colY_m L) (colFrame_m L) hc
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hdis := (GlobalTheory.StepLifts.places_apart L hL t).2
  have core := prodLev_inf_UA hbase (locPl G t) (fun w => rank_vertex G t w (X := (0, D.R.m)) ⟨h, le_rfl⟩)
    (fun w => givenLevel G t w (0, D.R.m))
    (Lev.datY (G.V (.grid 0 D.R.m)).rank D.R.r D.R.t D.R.m hr L.Pg (L.Q t) (LevelP.triv _ _ _) L.chi (L.xiR t) Lev.Frm.B) rfl
    (fun PP hP => Finset.mem_union_left _ (levelChainTypePlaces_subset_chosenPlaces G hL t hP)) (fun PP hP => Finset.mem_union_right _ hP)
    (fun w g => by
      rw [givenLevel_zero_iff G t w.1 D.R.m hm]
      by_cases hP : w.1 ∈ L.Pg
      · have hnq : w.1 ∉ L.Q t := Finset.disjoint_left.1 hdis hP
        rw [GlobalTheory.T.thetaGridBlockCongruence_typePrime_description G t w.1 hP]
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h1, fun _ => ⟨h2, h3⟩, fun hq => absurd hq hnq⟩
        · rintro ⟨h1, h2, -⟩
          exact ⟨h1, (h2 hP).1, (h2 hP).2⟩
      · rw [GlobalTheory.T.thetaGridBlockCongruence_offTypePrime_description G t w.1 hP]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, fun hp => absurd hp hP, h2⟩
        · rintro ⟨h1, -, h2⟩
          exact ⟨h1, h2⟩)
  have e1 : S.levRow t 0 h = prodLev (S.B.β 0 D.R.m) (locPl G t)
      (fun w => rank_vertex G t w (X := (0, D.R.m)) ⟨h, le_rfl⟩) (fun w => givenLevel G t w (0, D.R.m)) := rfl
  rw [e1, core]
  have key2 : ∀ (X : LSp D), X = ⟨D.sp.X', L.ΛX⟩ → ∀ (b : GL (Fin X.sp.rank) (Lev.EAf D)), HEq b L.βX →
      ∀ (hr : D.R.r ≤ X.sp.rank),
      HEq (lev D.sp.cm X.sp.gram b (Lev.datY X.sp.rank D.R.r D.R.t D.R.m hr L.Pg (L.Q t) (LevelP.triv _ _ _) L.chi (L.xiR t) Lev.Frm.B))
        (lev D.sp.cm D.sp.X'.gram L.βX (L.datXt t)) := by
    rintro X rfl b hb hr
    cases eq_of_heq hb
    rfl
  exact key2 (G.node (.grid 0 D.R.m)) (colY_m L) _ (colFrame_m L) hr

end GlobalTheory.FunObj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicCuspSectionsLeSpanAlgebraicCuspForms
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OntoCore

set_option maxHeartbeats 1000000 in

theorem holSub0_le_span_cuspA : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ w : WeightFamilies.Wt D j, w.LastPos → 8 * D.R.f * D.R.r + 4 ≤ w.n → ∀ σ, GoodEmb T.Q.c σ → Formalism.L2.Pj.holSub0 (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) ≤ Submodule.span ℂ (rdU (T.U j σ) '' (T.cuspA j (wtA w) w.n : Set (T.R j))) := by
  intro D T h j hj w hw hn σ hσ
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := Formalism.L2.Pj.hostSize_finrank D
  have hn' : 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ w.n := by
    rw [hfr]
    calc 4 * (2 * D.R.f * D.R.r) + 4 = 8 * D.R.f * D.R.r + 4 := by ring
      _ ≤ w.n := hn
  obtain ⟨hrk, hM⟩ := h.modelW j hj σ hσ
  have key := GlobalTheory.Dict.holSub0_le_span_cusp GlobalTheory.chartIndependence_unconditional D.host.E T.Q.H (T.Q.Dw j) T.Q.l
    (T.Q.Xo j) T.Q.c D.R.r (fun s => Formalism.L2.PjFree.Unf.ofPj (T.U j s)) hr h.pins.2.1.2
    (fun s hs => (Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj s hs)) σ hσ
    (fun k k' => ⟨(hM k).1.trans (hM k').1.symm, (hM k).2.trans (hM k').2.symm⟩)
    (fun k => GlobalTheory.PrincCore.mem_group_of_congruent D T.toCore h.toLawsM j hj σ hσ k)
    (wtA w) w.n (dom_wtA w) (GlobalTheory.lastPos_wtA_of_pins D T.Q h.pins j hj w hw) hn'
    (fun k => h.chiTriv j hj σ hσ (wtA w) w.n (dom_wtA w) k)
  intro P hP
  exact key ⟨hP.1, hP.2⟩

end GlobalTheory.OntoCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweSplittingActsFockActionPlusTraceMultiples
section
noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD

theorem lieScalarD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ)
    (om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)), IsCMExt F E σ → IsStd ψ →
    FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ → IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om →
    ∃ c, ActsByD τ C om Φ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) c := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ om hCM hψ hFr hΦ hom
  obtain ⟨ω₀, c₀, hH, hc, hact⟩ := GlobalTheory.T.exists_genuineSplitting_adelicSchwartz_placeSignature F E σ α β κ P Q R S ψ τ JA JB d a b A C Φ hCM hψ hFr hΦ
  obtain ⟨ν, hν, hmul, hνc, hν0⟩ := GlobalTheory.T.archimedean_splittings_differ_by_character F E σ α β κ ψ JA JB d om ω₀ hψ hom hH hc
  obtain ⟨k, hk⟩ := GlobalTheory.T.deriv_continuous_character_real_unitary_one_parameter F E σ β R S τ JB b C hCM hFr.2.2 ν hmul hνc hν0
  refine ⟨fun w => c₀ w + k w, ?_⟩
  intro γ hγ Y hY T g hg l hl
  have hH1 : ∀ t : ℝ, At (evI F) (((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)) - 1) := fun t => hγ.2 _
  have hpm : ∀ f : SInf F κ, pureA F f g ∈ schA F κ := fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
  have e1 : (fun t : ℝ => l (om (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) g))) =
      fun t => ν (γ (Multiplicative.ofAdd t)) * l (ω₀ (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) g)) := by
    funext t; rw [hν _ (hH1 t) _ (hpm _), map_smul, smul_eq_mul]
  show HasDerivAt (fun t : ℝ => l (om (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) g))) _ 0
  rw [e1]
  have h3 := (hk γ hγ Y hY).mul (hact γ hγ Y hY T g hg l hl)
  have hγ0 : γ (Multiplicative.ofAdd (0 : ℝ)) = 1 := by rw [ofAdd_zero, map_one]
  have h1m : At (evI F) (((1 : UG (cA σ) JB).1 : Matrix β β (AE F E)) - 1) := fun u _ => by simp
  have hν1 : ν 1 = 1 := by
    have := hmul 1 1 h1m h1m
    rw [mul_one] at this
    exact (mul_eq_left₀ (hν0 1 h1m)).mp this.symm
  beta_reduce at h3
  rw [hγ0, hν1, map_one, Module.End.one_apply, one_mul] at h3
  refine h3.congr_deriv ?_
  have e2 : sumPl (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w) +
        (((fun w => c₀ w + k w) w) * (Y w).trace) • (1 : Module.End ℂ _)) =
      sumPl (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w) + (c₀ w * (Y w).trace) • (1 : Module.End ℂ _)) +
        (∑ w, k w * (Y w).trace) • (1 : Module.End ℂ (TensD F P Q R S)) := by
    simp only [add_mul, add_smul, ← add_assoc]
    exact GlobalTheory.LieScal.sumPl_add_smul
      (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w) + (c₀ w * (Y w).trace) • (1 : Module.End ℂ _)) _
  rw [e2, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add, map_smul]
  have key : ∀ (z : ℂ) (f f' : SInf F κ), pureA F ⇑(f' + z • f) g = z • pureA F ⇑f g + pureA F ⇑f' g := by
    intro z f f'; funext x; simp [pureA]; ring
  rw [key, map_add, map_smul, smul_eq_mul]

end GlobalTheory.HoweD

end
end

