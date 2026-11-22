import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0650
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0218
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0634
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsLatticeVacuumIffSignedRationalFixed
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0386
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0186
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0649
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdaptedFrameOrthonormal
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.RowReal
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

theorem adaptedFrame_orthonormal {N r c N' : ℕ} (Γ : Matrix (Fin N) (Fin N) ℂ) (Γ' O : Matrix (Fin r) (Fin r) ℂ)
    (F : Matrix (Fin N) (Fin r) ℂ) (Zc : Matrix (Fin N) (Fin 1) ℂ) (hr : r = c) (hc : c + 1 = N') (hN : N = N')
    (hΓ : Γᴴ = Γ) (h1 : Fᴴ * Γ * F = Γ') (hO : Oᴴ * Γ' * O = 1) (h2 : Fᴴ * Γ * Zc = 0) (h3 : Zcᴴ * Γ * Zc = 1) :
    (Matrix.of (fun a k => Sum.elim (fun b : Fin c => (F * O) a (Fin.cast hr.symm b)) (fun _ : Fin 1 => Zc a 0)
      ((finSumFinEquiv.trans (finCongr hc)).symm (Fin.cast hN k))))ᴴ * Γ *
    Matrix.of (fun a k => Sum.elim (fun b : Fin c => (F * O) a (Fin.cast hr.symm b)) (fun _ : Fin 1 => Zc a 0)
      ((finSumFinEquiv.trans (finCongr hc)).symm (Fin.cast hN k))) = 1 := by
  subst hr hc hN
  set e := finSumFinEquiv (m := r) (n := 1)
  have hT : Matrix.of (fun a k => Sum.elim (fun b : Fin r => (F * O) a (Fin.cast rfl b)) (fun _ : Fin 1 => Zc a 0)
      ((e.trans (finCongr rfl)).symm (Fin.cast rfl k))) = (Matrix.fromCols (F * O) Zc).submatrix id e.symm := by
    ext a k
    simp only [Matrix.of_apply, Fin.cast_eq_self, Matrix.submatrix_apply, id]
    rcases h : e.symm k with b | b
    · simp [h, Matrix.fromCols]
    · simp [h, Matrix.fromCols, Subsingleton.elim b 0]
  have h4 : Zcᴴ * Γ * F = 0 := by
    have := congrArg Matrix.conjTranspose h2
    simpa [Matrix.conjTranspose_mul, hΓ, Matrix.mul_assoc] using this
  have a1 : ((Matrix.fromCols (F * O) Zc).submatrix id e.symm)ᴴ * Γ * (Matrix.fromCols (F * O) Zc).submatrix id e.symm =
      ((Matrix.fromCols (F * O) Zc)ᴴ * Γ * Matrix.fromCols (F * O) Zc).submatrix e.symm e.symm := rfl
  have b1 : (F * O)ᴴ * Γ * (F * O) = 1 := by
    rw [← hO, ← h1]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have b2 : (F * O)ᴴ * Γ * Zc = 0 := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Fᴴ, h2, Matrix.mul_zero]
  have b3 : Zcᴴ * Γ * (F * O) = 0 := by rw [← Matrix.mul_assoc, h4, Matrix.zero_mul]
  rw [hT, a1, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols,
    b1, b2, b3, h3, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem topFrame_orthonormal {μ0 : T} (hL : L.Is μ0) (W : G.Weil) (τ : D.what₂.Tau) :
    (topFrame W τ)ᴴ * gramAt D (G.V (.top D.R.m)) τ * topFrame W τ = 1 := by
  have hPt : PosOnb W (.top D.R.m) := posOnb_of_defNode W μ0 hL (X := .top D.R.m) le_rfl
  have hPg : PosOnb W (.grid D.R.m D.R.m) := posOnb_of_defNode W μ0 hL (X := .grid D.R.m D.R.m) ⟨le_rfl, rfl⟩
  have hm : ∀ {a b : ℕ} (X : Matrix (Fin (G.V (.top D.R.m)).rank) (Fin a) D.host.E)
      (Z : Matrix (Fin (G.V (.top D.R.m)).rank) (Fin b) D.host.E),
      (X.map (tauE D τ))ᴴ * gramAt D (G.V (.top D.R.m)) τ * Z.map (tauE D τ) =
        (Xᴴ * (G.V (.top D.R.m)).gram * Z).map (tauE D τ) := fun X Z => by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.conjTranspose_map _ (GlobalTheory.FockCompare.tauE_star τ)]; rfl
  have hΓ : (gramAt D (G.V (.top D.R.m)) τ)ᴴ = gramAt D (G.V (.top D.R.m)) τ := by
    have hB := hPt τ
    generalize W.onb (.top D.R.m) τ = B at hB
    generalize gramAt D (G.V (.top D.R.m)) τ = Γ at hB
    have hd : IsUnit B.det := Matrix.isUnit_det_of_left_inverse hB
    have h1 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
    have hG : Γ = (B⁻¹)ᴴ * B⁻¹ := by
      calc Γ = (B * B⁻¹)ᴴ * Γ * (B * B⁻¹) := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
        _ = (B⁻¹)ᴴ * (Bᴴ * Γ * B) * B⁻¹ := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [hB, Matrix.mul_one]
    rw [hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  refine adaptedFrame_orthonormal (c := (rowSizes D).nC D.R.m) _ (gramAt D (G.V (.grid D.R.m D.R.m)) τ) _ _ _
    (rank_gridM G (i := D.R.m) le_rfl) (rowSizes D).nC_succ (rank_top G (j := D.R.m) le_rfl) hΓ ?_ (hPg τ) ?_ ?_
  · exact (hm _ _).trans (congrArg (fun M => Matrix.map M (tauE D τ))
      (GlobalTheory.AutFunCounterexample.gram_pull (G.V (.top D.R.m)) (G.V (.grid D.R.m D.R.m)) G.sp.topDec.ι G.sp.topDec.isom))
  · refine (hm _ _).trans ((congrArg (fun M => Matrix.map M (tauE D τ)) G.sp.topDec.perp).trans ?_)
    ext i j; simp
  · refine (hm _ _).trans ((congrArg (fun M => Matrix.map M (tauE D τ)) G.sp.topDec.gram).trans ?_)
    ext i j
    obtain rfl := Subsingleton.elim i j
    simp [antiDiagonalSignGramMatrix]

theorem kappaTop_mul_topFrame {μ0 : T} (hL : L.Is μ0) (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (τ : D.what₂.Tau) :
    compAt W.θ τ (mt _ (kappaTop W g)) * topFrame W τ = topFrame W τ *
      (embed (rowSizes D).nC_succ (g.2 (Fin.last D.R.m)) τ).1.submatrix
        (Fin.cast (rank_top G (j := D.R.m) le_rfl)) (Fin.cast (rank_top G (j := D.R.m) le_rfl)) := by
  have hPg : PosOnb W (.grid (Fin.last D.R.m : Fin (D.R.m + 1)) D.R.m) :=
    posOnb_of_defNode W μ0 hL (X := .grid (Fin.last D.R.m : Fin (D.R.m + 1)) D.R.m) ⟨Nat.lt_succ_iff.1 (Fin.last D.R.m).2, rfl⟩
  have hdO : IsUnit (W.onb (.grid D.R.m D.R.m) τ).det := Matrix.isUnit_det_of_left_inverse (hPg τ)
  have h1 : compAt W.θ τ (mt (G.V (.top D.R.m)) (kappaTop W g)) *
      (frameMat (G.V (.top D.R.m)) (G.V (.grid D.R.m D.R.m)) G.sp.topDec.ι).map (tauE D τ) =
      (frameMat (G.V (.top D.R.m)) (G.V (.grid D.R.m D.R.m)) G.sp.topDec.ι).map (tauE D τ) *
        compAt W.θ τ (mt (G.V (.grid D.R.m D.R.m)) ((kappa W g).2 (Fin.last D.R.m))) := (archM_kappaTop W g τ).1
  have h3 : compAt W.θ τ (mt (G.V (.top D.R.m)) (kappaTop W g)) * G.sp.topDec.a.map (tauE D τ) =
      G.sp.topDec.a.map (tauE D τ) := (archM_kappaTop W g τ).2
  have h2 : compAt W.θ τ (mt (G.V (.grid D.R.m D.R.m)) ((kappa W g).2 (Fin.last D.R.m))) =
      W.onb (.grid D.R.m D.R.m) τ * (g.2 (Fin.last D.R.m) τ).1.submatrix (Fin.cast (rank_gridM G (i := D.R.m) le_rfl))
        (Fin.cast (rank_gridM G (i := D.R.m) le_rfl)) * (W.onb (.grid D.R.m D.R.m) τ)⁻¹ :=
    compAt_kappa_snd g (Fin.last D.R.m) hPg τ
  exact mul_adaptedFrame_of_blocks (c := (rowSizes D).nC D.R.m) _ _ _ _ _
    ((g.2 (Fin.last D.R.m) τ).1 : Matrix (Fin ((rowSizes D).nC D.R.m)) (Fin ((rowSizes D).nC D.R.m)) ℂ)
    (rank_gridM G (i := D.R.m) le_rfl) (rowSizes D).nC_succ (rank_top G (j := D.R.m) le_rfl) hdO h1 h2 h3

theorem exists_unitary_change {a b : ℕ} (h : a = b) {Γ B F : Matrix (Fin a) (Fin a) ℂ} (hB : Bᴴ * Γ * B = 1)
    (hF : Fᴴ * Γ * F = 1) : ∃ c : Matrix.unitaryGroup (Fin b) ℂ, ∀ (A : Matrix (Fin a) (Fin a) ℂ) (v : Matrix.unitaryGroup (Fin b) ℂ),
      A * F = F * v.1.submatrix (Fin.cast h) (Fin.cast h) →
      A = B * (c * v * c⁻¹).1.submatrix (Fin.cast h) (Fin.cast h) * B⁻¹ := by
  subst h
  have hd : IsUnit B.det := Matrix.isUnit_det_of_left_inverse hB
  have hdF : IsUnit F.det := Matrix.isUnit_det_of_left_inverse hF
  have h1 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have hu : (B⁻¹ * F)ᴴ * (B⁻¹ * F) = 1 := by
    calc (B⁻¹ * F)ᴴ * (B⁻¹ * F) = (B⁻¹ * F)ᴴ * (Bᴴ * Γ * B) * (B⁻¹ * F) := by rw [hB, Matrix.mul_one]
      _ = Fᴴ * ((B * B⁻¹)ᴴ * Γ * (B * B⁻¹)) * F := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hF]
  have hu' : (B⁻¹ * F) * (B⁻¹ * F)ᴴ = 1 := mul_eq_one_comm.1 hu
  refine ⟨⟨B⁻¹ * F, Matrix.mem_unitaryGroup_iff'.2 hu⟩, fun A v hA => ?_⟩
  have hA' : A * F = F * v.1 := hA
  show A = B * (B⁻¹ * F * v.1 * (B⁻¹ * F)ᴴ) * B⁻¹
  calc A = A * (B * ((B⁻¹ * F) * (B⁻¹ * F)ᴴ) * B⁻¹) := by rw [hu', Matrix.mul_one, h1, Matrix.mul_one]
    _ = A * (B * B⁻¹) * F * (B⁻¹ * F)ᴴ * B⁻¹ := by simp only [Matrix.mul_assoc]
    _ = (B * B⁻¹) * (F * v.1) * (B⁻¹ * F)ᴴ * B⁻¹ := by rw [h1, Matrix.mul_one, Matrix.one_mul, hA']
    _ = _ := by simp only [Matrix.mul_assoc]

theorem exists_ptTop_conj {μ0 : T} (hL : L.Is μ0) (W : G.Weil) (n : Fin (D.R.m + 1)) :
    ∃ c : UG D.what₂.Tau ((rowSizes D).nR n), ∀ (g : Gc D.what₂.Tau (rowSizes D)) τ,
      compAt W.θ τ (mt _ (ptTop W g n)) = W.onb (.top n) τ *
        ((c * rowComp (rowSizes D) g n * c⁻¹) τ).1.submatrix (Fin.cast (rank_top G (Nat.lt_succ_iff.1 n.2)))
          (Fin.cast (rank_top G (Nat.lt_succ_iff.1 n.2))) * (W.onb (.top n) τ)⁻¹ := by
  have hP : PosOnb W (.top n) := posOnb_of_defNode W μ0 hL (X := .top n) (Nat.lt_succ_iff.1 n.2)
  by_cases h : (n : ℕ) = D.R.m
  · obtain rfl : n = Fin.last D.R.m := Fin.ext h
    choose c hc using fun τ => exists_unitary_change (rank_top G (j := D.R.m) le_rfl) (hP τ) (topFrame_orthonormal hL W τ)
    refine ⟨c, fun g τ => ?_⟩
    have hlast : rowComp (rowSizes D) g (Fin.last D.R.m) = embed (rowSizes D).nC_succ (g.2 (Fin.last D.R.m)) := by
      simp only [rowComp, MonoidHom.coe_mk, OneHom.coe_mk]
      exact Fin.snoc_last (α := fun j : Fin ((rowSizes D).m + 1) => UG D.what₂.Tau ((rowSizes D).nR j)) _ _
    rw [show ptTop W g ((Fin.last D.R.m : Fin (D.R.m + 1)) : ℕ) = kappaTop W g from ptTop_m W g]
    erw [hlast]
    exact hc τ _ _ (kappaTop_mul_topFrame hL W g τ)
  · refine ⟨1, fun g τ => ?_⟩
    rw [one_mul, inv_one, mul_one]
    exact eq_conj_of_inFrame (Matrix.isUnit_det_of_left_inverse (hP τ)) (GlobalTheory.T.compactChainTopRowRealPoint_inOrthonormalBasis hL W g n (fun e => absurd e h) τ)

def trColEquiv (G : GridData L sc) (j : Fin D.R.m) :
    PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank ≃ₗ[ℂ] Pol D.what₂.Tau ((rowSizes D).nR j) ((rowSizes D).nR (j + 1)) :=
  LinearEquiv.ofBijective (trCol G j).toLinearMap ⟨trCol_injective G j, MvPolynomial.rename_surjective _ fun y =>
    ⟨(y.1, Fin.cast (rank_top G (j := (j : ℕ) + 1) j.2).symm y.2.1, Fin.cast (rank_top G j.2.le).symm y.2.2), rfl⟩⟩

def trRowEquiv (G : GridData L sc) (i : Fin D.R.m) :
    PolF D (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank ≃ₗ[ℂ]
      Pol D.what₂.Tau ((rowSizes D).nC i) ((rowSizes D).nC (i + 1)) :=
  LinearEquiv.ofBijective (trRow G i).toLinearMap ⟨trRow_injective G i, MvPolynomial.rename_surjective _ fun y =>
    ⟨(y.1, Fin.cast (rank_gridM G i.2.le).symm y.2.2, Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2).symm y.2.1), rfl⟩⟩

def subEquiv {ι : Type} [Fintype ι] {a b : ℕ} (x : UG ι a × UG ι b) : Pol ι a b ≃ₗ[ℂ] Pol ι a b :=
  LinearEquiv.ofLinear (linSub (homMat a b x)) (linSub (homMat a b x⁻¹))
    (by rw [← Module.End.mul_eq_comp, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]; rfl)

theorem linSub_homMat_mul {ι : Type} [Fintype ι] {a b : ℕ} (x y : UG ι a × UG ι b) (p : Pol ι a b) :
    linSub (homMat a b x) (linSub (homMat a b y) p) = linSub (homMat a b (x * y)) p := by
  rw [map_mul, map_mul]; rfl

theorem om_fock_top_of_mat {μ0 : T} (hL : L.Is μ0) (W : G.Weil) {U : Set T} (S : GridChoice W U)
    (g : Gc D.what₂.Tau (rowSizes D)) (t : T) (j : Fin D.R.m)
    (u : UG D.what₂.Tau ((rowSizes D).nR j)) (v : UG D.what₂.Tau ((rowSizes D).nR (j + 1)))
    (c1 : ∀ τ, compAt W.θ τ (mt _ (ptTop W g j)) = W.onb (.top (j : ℕ)) τ *
      (u τ).1.submatrix (Fin.cast (rank_top G (j := j) j.2.le)) (Fin.cast (rank_top G (j := j) j.2.le)) *
      (W.onb (.top (j : ℕ)) τ)⁻¹)
    (c2 : ∀ τ, compAt W.θ τ (mt _ (ptTop W g ((j : ℕ) + 1))) = W.onb (.top ((j : ℕ) + 1)) τ *
      (v τ).1.submatrix (Fin.cast (rank_top G (j := (j : ℕ) + 1) j.2)) (Fin.cast (rank_top G (j := (j : ℕ) + 1) j.2)) *
      (W.onb (.top ((j : ℕ) + 1)) τ)⁻¹)
    (d : FinDatum G t (.top t j)) (hd : S.Z.HasVec d) (Q Q' : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank)
    (hQ : trCol G j Q' = rowScal (rowEntries D sc.cGap) j g • linSub (homMat _ _ (u, v)) (trCol G j Q)) :
    W.om (.top t j) (G.toPair (.top t j) (ptTop W g j) (ptTop W g (j + 1))) (W.fock (.top t j) (movedVec t S d) Q) =
      W.fock (.top t j) (movedVec t S d) Q' := by
  have hX : DefNode D.R.m (.top (j : ℕ)) := j.2.le
  have hY : DefNode D.R.m (.top ((j : ℕ) + 1)) := j.2
  have hp : DefPair D.R.m (Pair.top t (j : ℕ)) := j.2
  obtain ⟨hf, hv⟩ := GlobalTheory.T.movedVector_definitePair_theta_fockVacuum W S t (.top t j) hp d hd
  have hc := GlobalTheory.T.compactChain_topPair_movedVector_rowCharacter hL W S g t j d hd
  have key := GlobalTheory.T.weil_compactRealPoint_fockVector_substitution W (.top t j) j.2 (fun _ => (G.V (.top (j : ℕ))).rank) (fun _ => (G.V (.top ((j : ℕ) + 1))).rank)
    (fun _ => le_rfl) (fun _ => le_rfl) (fun ρ => (GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces hL W _ hX ρ).1) (fun ρ => (GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces hL W _ hY ρ).1)
    (fun ρ => (GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces hL W _ hX ρ).2.1) (fun ρ => (GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces hL W _ hY ρ).2.1) _ hf hv
    (fun τ => (u τ).1.submatrix (Fin.cast (rank_top G (j := j) j.2.le)) (Fin.cast (rank_top G (j := j) j.2.le)))
    (fun τ => (v τ).1.submatrix (Fin.cast (rank_top G (j := (j : ℕ) + 1) j.2)) (Fin.cast (rank_top G (j := (j : ℕ) + 1) j.2)))
    (fun ρ => isKMat_cast _ _ (Or.inl rfl)) (fun ρ => isKMat_cast _ _ (Or.inl rfl))
    (ptTop W g j) (ptTop W g (j + 1)) (ptTop_mem W g _) (ptTop_mem W g _) c1 c2 _ hc Q
  have hQ' : Q' = rowScal (rowEntries D sc.cGap) j g • fockSubAll (fun _ => (G.V (.top (j : ℕ))).rank)
      (fun _ => (G.V (.top ((j : ℕ) + 1))).rank)
      (fun τ => (u τ).1.submatrix (Fin.cast (rank_top G (j := j) j.2.le)) (Fin.cast (rank_top G (j := j) j.2.le)))
      (fun τ => (v τ).1.submatrix (Fin.cast (rank_top G (j := (j : ℕ) + 1) j.2)) (Fin.cast (rank_top G (j := (j : ℕ) + 1) j.2)))
      Q := by
    apply trCol_injective G j
    rw [hQ, map_smul, GlobalTheory.T.fockSubstitution_rowStep_rename_unitary G j u v Q]
  show W.om (.top t j) (ptTop W g j, ptTop W g (j + 1)) _ = _
  rw [key, hQ', LinearMap.map_smul]

theorem exists_fock_transport : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T} (hL : L.Is μ0)
    (W : G.Weil), ∃ (tc : ∀ j : Fin D.R.m, PolF D (G.V (.top ((j : ℕ) + 1))).rank (G.V (.top j)).rank ≃ₗ[ℂ]
        Pol D.what₂.Tau ((rowSizes D).nR (j.castSucc : Fin ((rowSizes D).m + 1))) ((rowSizes D).nR (j.succ : Fin ((rowSizes D).m + 1))))
      (tr : ∀ i : Fin D.R.m, PolF D (G.V (.grid i D.R.m)).rank (G.V (.grid ((i : ℕ) + 1) D.R.m)).rank ≃ₗ[ℂ]
        Pol D.what₂.Tau ((rowSizes D).nC (i.castSucc : Fin ((rowSizes D).m + 1))) ((rowSizes D).nC (i.succ : Fin ((rowSizes D).m + 1)))),
      ∀ {U : Set T} (S : GridChoice W U) (g : Gc D.what₂.Tau (rowSizes D)) (t : T),
        (∀ (j : Fin D.R.m) (d : FinDatum G t (.top t j)), S.Z.HasVec d → ∀ Q,
          W.om (.top t j) (G.toPair (.top t j) (ptTop W g j) (ptTop W g (j + 1))) (W.fock (.top t j) (movedVec t S d) Q) =
            W.fock (.top t j) (movedVec t S d) ((tc j).symm (rowFock (rowEntries D sc.cGap) j g (tc j Q)))) ∧
        (∀ (i : Fin D.R.m) (d : FinDatum G t (.chi i D.R.m)), S.Z.HasVec d → ∀ Q,
          W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) (ptGrid W g i) (ptGrid W g (i + 1)))
              (W.fock (.chi i D.R.m) (movedVec t S d) Q) =
            W.fock (.chi i D.R.m) (movedVec t S d) ((tr i).symm (colFock (rowEntries D sc.cGap) i g (tr i Q)))) := by
  intro D T L sc G μ0 hL W
  choose c hc using exists_ptTop_conj hL W
  refine ⟨fun j => (trColEquiv G j).trans (subEquiv (c j.castSucc, c j.succ)).symm, fun i => trRowEquiv G i,
    fun S g t => ⟨fun j d hd Q => ?_, fun i d hd Q => ?_⟩⟩
  · refine om_fock_top_of_mat hL W S g t j _ _ (hc j.castSucc g) (hc j.succ g) d hd Q _ ?_
    have e : ∀ y, trCol G j ((trColEquiv G j).symm y) = y := fun y => (trColEquiv G j).apply_symm_apply y
    refine (e _).trans ?_
    show linSub (homMat _ _ (c j.castSucc, c j.succ)) (rowScal (rowEntries D sc.cGap) j g •
      linSub (homMat _ _ (rowComp (rowSizes D) g j.castSucc, rowComp (rowSizes D) g j.succ))
        (linSub (homMat _ _ (c j.castSucc, c j.succ)⁻¹) (trCol G j Q))) = _
    rw [LinearMap.map_smul, linSub_homMat_mul, linSub_homMat_mul]
    rfl
  · exact om_fock_chi hL W S g t i d hd Q _ ((trRowEquiv G i).apply_symm_apply _)

end GlobalTheory.RowReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointFrameRowReductionEqZeroIffMem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LiftDat.RowKer

open GlobalTheory.LiftLevel

variable {D : D7}

theorem row_mat {S T : HSp D} (hS : S.gram = 1) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (a e : AE D) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    adjA S T βS βT a (partAt (cA D e) (finW S T y)) = Matrix.of fun i j => rowAdj T βT a e (y i) 0 j := by
  have hb : βS.val * (βS⁻¹).val = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hg : (S.gram⁻¹).map (incA D) = 1 := by rw [hS, inv_one, Matrix.map_one _ (map_zero _) (map_one _)]
  unfold adjA frMapAdj rowAdj
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hb, Matrix.one_mul, hg, Matrix.one_mul]
  ext i j
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply,
    partAt, finW, smul_eq_mul, Fin.sum_univ_one, map_sum]

theorem rowRed_zero (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (a e : AE D) (PP : Formalism.L2.DIV.Pl D.host.E) :
    rowRed T βT a e PP 0 = 0 := by
  funext j
  have h0 : rowAdj T βT a e 0 = 0 := by
    unfold rowAdj; ext i k; simp [Matrix.mul_apply, Matrix.smul_apply]
  have h1 : ∀ h, Formalism.L2.DIV.resS D.host.F PP (⟨0, h⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = 0 :=
    fun _ => map_zero _
  simp [rowRed, redM, h0, h1]

theorem full_std (n : ℕ) : (stdL D.host.E n).FG ∧
    Submodule.span D.host.E (stdL D.host.E n : Set (Fin n → D.host.E)) = ⊤ := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin n)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span ⟨a, by simp⟩

theorem full_smul {r : ℕ} (I : Ideal (𝓞 D.host.E)) (hI : I ≠ ⊥) (L : Lt D.host.E r) (hL : L.FG)
    (hLs : Submodule.span D.host.E (L : Set (Fin r → D.host.E)) = ⊤) :
    (I • L).FG ∧ Submodule.span D.host.E ((I • L : Lt D.host.E r) : Set (Fin r → D.host.E)) = ⊤ := by
  refine ⟨hL.smul (IsNoetherian.noetherian I), ?_⟩
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have htE : (t : D.host.E) ≠ 0 := fun h => ht0 (RingOfIntegers.ext (h.trans rfl))
  rw [eq_top_iff, ← hLs, Submodule.span_le]
  intro u hu
  have hu' : (t : D.host.E) • u ∈ Submodule.span D.host.E ((I • L : Lt D.host.E r) : Set (Fin r → D.host.E)) :=
    Submodule.subset_span (Submodule.smul_mem_smul ht hu)
  have := Submodule.smul_mem _ ((t : D.host.E)⁻¹) hu'
  rwa [smul_smul, inv_mul_cancel₀ htE, one_smul] at this

end GlobalTheory.LiftDat.RowKer

namespace GlobalTheory.LiftDat.RowKer

open GlobalTheory.LiftLevel

theorem rowRed_eq_zero_iff : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) → ∀ v ∈ C.X.Λ, ((∀ PP ∈ Pg ∪ Q, GlobalTheory.LiftDat.rowRed T βT a e PP v = 0) ↔ v ∈ GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ) := by
  intro D S T C hn ΛT _ _ βS βT _ _ Pg Q ξ _ _ e he a k₀ _ _ hgen h1 h2 h3 _ v hv
  rcases Nat.eq_zero_or_pos T.rank with h0 | hpos
  · haveI : IsEmpty (Fin T.rank) := by rw [h0]; infer_instance
    have hv0 : v = 0 := funext fun j => isEmptyElim j
    constructor
    · intro _; rw [hv0]; exact zero_mem _
    · intro _ PP _; funext j; exact isEmptyElim j
  let i0 : Fin S.rank := ⟨0, lt_of_lt_of_le hpos hn⟩
  let y : Matrix (Fin S.rank) (Fin T.rank) D.host.E := Matrix.of fun i => if i = i0 then v else 0
  have hyrow : ∀ i, y i = if i = i0 then v else 0 := fun i => rfl
  have hy0 : y i0 = v := by rw [hyrow, if_pos rfl]
  have hy : ∀ L : Lt D.host.E T.rank, v ∈ L → y ∈ tens (stdL D.host.E S.rank) L := fun L hvL =>
    (GlobalTheory.SW.TensLat.mem_tens_stdL L y).2 fun k => by
      rw [hyrow]
      split_ifs
      · exact hvL
      · exact zero_mem _
  have hAo : ∀ L : Lt D.host.E T.rank, ∀ o : 𝓞 D.host.E, ∀ z ∈ tens (stdL D.host.E S.rank) L,
      (o : D.host.E) • z ∈ tens (stdL D.host.E S.rank) L :=
    fun L o z hz => smul_mem_tens o (fun u hu => Submodule.smul_mem _ o hu) hz
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hce : finPart D (cA D e) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by
      rw [← map_mul, ← map_mul, hee])
  have hfinW : ∀ (L : Lt D.host.E T.rank) (z : Matrix (Fin S.rank) (Fin T.rank) D.host.E),
      z ∈ tens (stdL D.host.E S.rank) L → finW S T z ∈ hatA S T (tens (stdL D.host.E S.rank) L) := fun L z hz => by
    rw [GlobalTheory.Ker.SignVac.finW_eq]; exact GlobalTheory.Ker.SignVac.finTens_mem (GlobalTheory.LatVac.one_mem_intAf _) hz
  have hxL : ∀ L : Lt D.host.E T.rank, v ∈ L →
      partAt (cA D e) (finW S T y) ∈ hatA S T (tens (stdL D.host.E S.rank) L) := fun L hvL => by
    have : partAt (cA D e) (finW S T y) = cA D e • finW S T y := by ext i j; rfl
    rw [this]; exact smul_mem_hatA_of_int (hAo L) hce (hfinW L y (hy L hvL))
  have hhalf : IsHalf (cA D e) (partAt (cA D e) (finW S T y)) := fun i j => by
    simp only [partAt, Matrix.map_apply, ← mul_assoc, ← map_mul, hee]
  obtain ⟨hc1, hc2⟩ := hgen _ hhalf
  have hred : ∀ PP, redM PP (adjA S T βS βT a (partAt (cA D e) (finW S T y))) =
      fun i j => rowRed T βT a e PP (y i) j := by
    intro PP; rw [row_mat C.m.gS βS βT a e y]; rfl
  constructor
  · intro hR
    have hint := hc1.2 (hxL _ hv)
    have hall : ∀ PP ∈ Pg ∪ Q, redM PP (adjA S T βS βT a (partAt (cA D e) (finW S T y))) = 0 := by
      intro PP hPP
      rw [hred]
      funext i j
      rw [hyrow]
      split_ifs
      · exact congrFun (hR PP hPP) j
      · exact congrFun (rowRed_zero T βT a e PP) j
    have hxI := hc2.1 ⟨hint, hall⟩

    have hm : liftI Pg Q ⊔ conjI (liftI Pg Q) = ⊤ := Ideal.isCoprime_iff_sup_eq.1 h3
    have h1' : (1 : 𝓞 D.host.E) ∈ liftI Pg Q ⊔ conjI (liftI Pg Q) := by rw [hm]; exact Submodule.mem_top
    obtain ⟨t, ht, c, hc, htc⟩ := Submodule.mem_sup.1 h1'
    have hcP : ∀ PP ∈ Pg ∪ Q, conjI (liftI Pg Q) ≤ PP.asIdeal := by
      intro PP hPP x hx
      have h2' := mem_of_mem_conjI hx
      rw [liftI] at h2'
      have h3' : stO x ∈ conjI PP.asIdeal := Finset.inf_le (f := fun PP : Formalism.L2.DIV.Pl D.host.E => conjI PP.asIdeal)
        hPP (Ideal.prod_le_inf h2')
      have h4' := mem_of_mem_conjI h3'
      have h5' : stO (stO x) = x := RingOfIntegers.ext (star_star _)
      rwa [h5'] at h4'
    have htP : ∀ PP ∈ Pg ∪ Q, t ∉ PP.asIdeal := by
      intro PP hPP htm
      have h6 : (1 : 𝓞 D.host.E) ∈ PP.asIdeal := htc ▸ add_mem htm (hcP PP hPP hc)
      exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h6)
    have hPQ : (Pg ∪ Q).Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      apply h1
      rw [liftI, hne, Finset.prod_empty, Ideal.one_eq_top]
    have ht0 : (t : D.host.E) ≠ 0 := by
      obtain ⟨PP, hPP⟩ := hPQ
      intro h
      apply htP PP hPP
      have : t = 0 := RingOfIntegers.ext (h.trans rfl)
      rw [this]; exact zero_mem _
    have htL : ∀ u ∈ C.X.Λ, t • u ∈ liftI Pg Q • C.X.Λ := fun u hu => Submodule.smul_mem_smul ht hu
    have hty : (t : D.host.E) • y ∈ tens (stdL D.host.E S.rank) (liftI Pg Q • C.X.Λ) := smul_mem_tens t htL (hy _ hv)
    have hz1 : finPart D (e * incA D ((t : D.host.E))⁻¹) ∈ intAE D :=
      GlobalTheory.IdemSumInt.finPart_idemSum_mul_inv_mem D e (Pg ∪ Q) he t htP
    have e1 : partAt e (finW S T y) = (e * incA D ((t : D.host.E))⁻¹) • finW S T ((t : D.host.E) • y) := by
      have e2 : finW S T ((t : D.host.E) • y) =
          (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (t : D.host.E) : AE D) • finW S T y := by
        rw [GlobalTheory.Ker.SignVac.finW_eq, GlobalTheory.Ker.SignVac.finW_eq, GlobalTheory.LatVac.tmul_smul_finTens, one_mul,
          Matrix.transpose_smul]
      have e3 : finW S T y = (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) • finW S T y := by
        rw [GlobalTheory.Ker.SignVac.finW_eq, GlobalTheory.LatVac.tmul_smul_finTens, one_mul, one_smul]
      rw [e2, smul_smul, mul_assoc]
      have e4 : incA D ((t : D.host.E))⁻¹ * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (t : D.host.E) : AE D) =
          pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E) := by
        change ((1 : AF D.host.F) ⊗ₜ[D.host.F] ((t : D.host.E))⁻¹) * _ = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ ht0]
      rw [e4, mul_smul, ← e3]
      ext i j; rfl
    have hpe : partAt e (finW S T y) ∈ hatA S T (tens (stdL D.host.E S.rank) (liftI Pg Q • C.X.Λ)) := by
      rw [e1]; exact smul_mem_hatA_of_int (hAo _) hz1 (hfinW _ _ hty)

    have hpo := GlobalTheory.T.offIdempotent_finitePoint_mem_completedTensorLattice D S T Pg Q e he C.X.Λ y (hy _ hv)
    have hsum : finW S T y = partAt (cA D e) (finW S T y) + partAt e (finW S T y) +
        partAt (1 - e - cA D e) (finW S T y) := by
      ext i j; simp only [partAt, Matrix.add_apply, Matrix.map_apply]; ring
    have hfI : finW S T y ∈ hatA S T (tens (stdL D.host.E S.rank) (liftI Pg Q • C.X.Λ)) := by
      rw [hsum]; exact add_mem (add_mem hxI hpe) hpo
    have hyI := ((GlobalTheory.Ker.HatLat.hatA_tens D S T C (stdL D.host.E S.rank) (liftI Pg Q • C.X.Λ) (full_std _)
      (full_smul _ h2 C.X.Λ C.X.Λ_fg C.X.Λ_span)).2.1 y).1 hfI
    have := (GlobalTheory.SW.TensLat.mem_tens_stdL _ y).1 hyI i0
    rwa [hy0] at this
  · intro hvI PP hPP
    have h6 := (hc2.2 (hxL _ hvI)).2 PP hPP
    rw [hred] at h6
    funext j
    have h7 := congrFun (congrFun h6 i0) j
    rw [hy0] at h7
    exact h7

end GlobalTheory.LiftDat.RowKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesPerHaarScale
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.Per

theorem besPer_haar_scale : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ {A B : HSp D} {c : ℕ} {ε : D.host.E} (a : HermitianOrthogonalExtensionData A B c ε) (dd : BesDat A B a.ι), GlobalTheory.Unf.CoCpt A → ∀ (μ μ' : Measure (GA D A)) (𝓕 𝓕' : Set (GA D A)) (ν ν' : Measure (NFlag B dd.e)) (𝓝 𝓝' : Set (NFlag B dd.e)), μ.IsHaarMeasure → IsFundamentalDomain (GQ A) 𝓕 μ → μ'.IsHaarMeasure → IsFundamentalDomain (GQ A) 𝓕' μ' → GlobalTheory.Per.IsUnitN B dd.e ν 𝓝 → GlobalTheory.Per.IsUnitN B dd.e ν' 𝓝' → ∀ (φ : GA D A → ℂ) (F : GA D B → ℂ), (∀ γ ∈ GQ A, ∀ g, φ (γ * g) = φ g) → (∀ γ ∈ GQ B, ∀ g, F (γ * g) = F g) → ∃ r : ℝ, 0 < r ∧ GlobalTheory.Per.besPer ψ dd μ 𝓕 ν 𝓝 (stabilizerEmbedding a) φ F = r * GlobalTheory.Per.besPer ψ dd μ' 𝓕' ν' 𝓝' (stabilizerEmbedding a) φ F := by
  intro D ψ hψ A B c ε a dd _ μ μ' 𝓕 𝓕' ν ν' 𝓝 𝓝' hμ h𝓕 hμ' h𝓕' hN hN' φ F hφ hF
  obtain ⟨_, _, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨-, -, -, -, _, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  obtain ⟨_, _, _, _⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag B dd.e_iso
  obtain ⟨s, -, hs, hq⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A a.ι a.isom
  have hsa : stabilizerEmbedding a = s := funext fun h => ((embRel_iff a h _).1 ((hs _ _).2 rfl)).symm

  have hl : ∀ h, ∀ γ ∈ NFlagQ B dd.e, ∀ n : NFlag B dd.e,
      besFun ψ dd (stabilizerEmbedding a) φ F h (γ * n) = besFun ψ dd (stabilizerEmbedding a) φ F h n := by
    intro h γ hγ n
    simp only [besFun, Subgroup.coe_mul]
    rw [GlobalTheory.BesselChar.besChar_mul ψ dd γ n γ.2 n.2, GlobalTheory.BesselChar.besChar_rat ψ hψ.1 dd γ γ.2 hγ, one_mul,
      mul_assoc (γ : GA D B), mul_assoc (γ : GA D B), hF (γ : GA D B) hγ]

  have e1 : ∀ h, ∫ n in 𝓝, besFun ψ dd (stabilizerEmbedding a) φ F h n ∂ν = ∫ n in 𝓝', besFun ψ dd (stabilizerEmbedding a) φ F h n ∂ν' :=
    fun h => GlobalTheory.Mem.TrueRecord.integral_unit _ hN.1 hN.2.1 hN.2.2 hN'.1 hN'.2.1 hN'.2.2 _ (hl h)

  have e2 : ∀ γ ∈ GQ A, ∀ g, ∫ n in 𝓝, besFun ψ dd (stabilizerEmbedding a) φ F (γ * g) n ∂ν =
      ∫ n in 𝓝, besFun ψ dd (stabilizerEmbedding a) φ F g n ∂ν := by
    intro γ hγ g
    have r2 : EmbRel B A a.ι (s γ)⁻¹ γ⁻¹ := (hs _ _).2 (map_inv s _).symm
    have r1 : EmbRel B A a.ι (s γ) γ := (hs _ _).2 rfl
    let k : NFlag B dd.e ≃ₜ* NFlag B dd.e :=
      { toFun := fun n => ⟨(s γ)⁻¹ * n * (s γ)⁻¹⁻¹, (GlobalTheory.BesselChar.besChar_conj ψ dd _ _ r2 n n.2).1⟩
        invFun := fun n => ⟨s γ * n * (s γ)⁻¹, (GlobalTheory.BesselChar.besChar_conj ψ dd _ _ r1 n n.2).1⟩
        left_inv := fun n => Subtype.ext (by simp [mul_assoc])
        right_inv := fun n => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun x y => Subtype.ext (by simp [mul_assoc])
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    have hk : ∀ n, k n ∈ NFlagQ B dd.e ↔ n ∈ NFlagQ B dd.e := fun n => by
      change (s γ)⁻¹ * (n : GA D B) * (s γ)⁻¹⁻¹ ∈ GQ B ↔ (n : GA D B) ∈ GQ B
      rw [Subgroup.mul_mem_cancel_right _ (inv_mem (inv_mem (hq _ hγ))),
        Subgroup.mul_mem_cancel_left _ (inv_mem (hq _ hγ))]
    refine Eq.trans ?_ (GlobalTheory.Mem.TrueRecord.integral_aut _ hN.1 hN.2.1 hN.2.2 k hk _ (hl g))
    congr 1
    funext n
    have hc := (GlobalTheory.BesselChar.besChar_conj ψ dd _ _ r2 n n.2).2
    simp only [besFun, k, ContinuousMulEquiv.coe_mk, MulEquiv.coe_mk, Equiv.coe_fn_mk]
    rw [hc, hsa, hφ γ hγ, map_mul, ← hF _ (inv_mem (hq γ hγ)) ((n : GA D B) * (s γ * s g) * (dd.y : GA D B))]
    simp only [mul_assoc, inv_inv]

  have hc := Measure.haarScalarFactor_pos_of_isHaarMeasure μ μ'
  have e := Measure.isMulLeftInvariant_eq_smul μ μ'
  have hac : μ' ≪ μ := by
    intro t ht
    rw [e, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_eq_zero] at ht
    exact ht.resolve_left (by simpa using hc.ne')
  have h𝓕₁ : IsFundamentalDomain (GQ A) 𝓕 μ' := h𝓕.mono hac
  refine ⟨(μ.haarScalarFactor μ' : ℝ), by exact_mod_cast hc, ?_⟩
  show ∫ h in 𝓕, ∫ n in 𝓝, besFun ψ dd (stabilizerEmbedding a) φ F h n ∂ν ∂μ =
    _ * ∫ h in 𝓕', ∫ n in 𝓝', besFun ψ dd (stabilizerEmbedding a) φ F h n ∂ν' ∂μ'
  simp_rw [← e1]
  rw [← h𝓕₁.setIntegral_eq h𝓕' (fun γ g => e2 γ γ.2 g)]
  conv_lhs => rw [e]
  rw [Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

end GlobalTheory.Per
end
end

