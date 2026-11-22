import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0041
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0003
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0040
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0035
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0042
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0038
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0033
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.UnipotentPartBlockMatrix
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0029
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0005
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0008
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0034
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilThetaConvergence.WeilThetaConvergenceOfSiegelSet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitary

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayAC
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

namespace PositivityTheory.Rg.Sw.Glob.AW

variable {D : D7} {n : ℕ}

theorem gens_inv (g : G D n)
    (hg : (∃ b, mat g⁻¹ = blk4 1 b 0 1) ∨ (∃ a d, mat g⁻¹ = blk4 a 0 0 d) ∨ (∃ c, mat g⁻¹ = blk4 1 0 c 1)) :
    (∃ b, mat g = blk4 1 b 0 1) ∨ (∃ a d, mat g = blk4 a 0 0 d) ∨ (∃ c, mat g = blk4 1 0 c 1) := by
  have hgg : g = (g⁻¹)⁻¹ := (inv_inv g).symm
  rcases hg with ⟨b, hb⟩ | ⟨a, d, h⟩ | ⟨c, hc⟩
  · refine Or.inl ⟨-adj b, ?_⟩
    rw [hgg, GlobalTheory.CompanionTheory.SwUnf.SmallCell.mat_inv _ hb]; simp [adj_one, adj_zero]
  · refine Or.inr (Or.inl ⟨adj d, adj a, ?_⟩)
    rw [hgg, GlobalTheory.CompanionTheory.SwUnf.SmallCell.mat_inv _ h]; simp [adj_zero]
  · refine Or.inr (Or.inr ⟨-adj c, ?_⟩)
    rw [hgg, GlobalTheory.CompanionTheory.SwUnf.SmallCell.mat_inv _ hc]; simp [adj_one, adj_zero]

theorem closure_triv (hG : GenA) (hDA : DecompAway) {θ : InfFam D} {τ : D.what₂.Tau} {ι : GR n →* G D n}
    (hθ : IsInfFam θ) (hι : IsPlaceEmb θ τ ι) (x : G D n) (hx : IsTrivAt θ τ x) :
    x ∈ Submonoid.closure {x : G D n | IsTrivAt θ τ x ∧
      ((∃ b, mat x = blk4 1 b 0 1) ∨ (∃ a d, mat x = blk4 a 0 0 d) ∨ (∃ c, mat x = blk4 1 0 c 1))} := by
  classical
  choose π yf hπ using fun g => hDA D n θ τ ι hθ hι g
  have πmul : ∀ g h : G D n, π (g * h) = π g * π h := by
    intro g h
    have e1 := (hπ (g * h)).2.1
    have hg := (hπ g).2.1
    have hh := (hπ h).2.1
    have hc := (hπ h).2.2 (yf g)
    have e2 : g * h = (π g * π h) * ι (yf g * yf h) := by
      calc g * h = π g * ι (yf g) * (π h * ι (yf h)) := by rw [← hg, ← hh]
        _ = π g * (ι (yf g) * π h) * ι (yf h) := by group
        _ = π g * (π h * ι (yf g)) * ι (yf h) := by rw [hc]
        _ = (π g * π h) * ι (yf g * yf h) := by rw [map_mul]; group
    have e3 : π (g * h) * ι (yf (g * h)) = (π g * π h) * ι (yf g * yf h) := e1.symm.trans e2
    have hy := uniq_dec hι (hπ (g * h)).1 (triv_mul (hπ g).1 (hπ h).1) e3
    rw [hy] at e3
    exact mul_right_cancel e3
  have πtriv : ∀ a, IsTrivAt θ τ a → π a = a := by
    intro a ha
    have e1 := (hπ a).2.1
    have hy := uniq_dec hι (hπ a).1 ha (show π a * ι (yf a) = a * ι 1 by rw [← e1, map_one, mul_one])
    rw [hy, map_one, mul_one] at e1
    exact e1.symm
  have fz : ((0 : Mx D n n)).map (finPart D) = 0 := Matrix.map_zero _ (map_zero _)
  have fo : ((1 : Mx D n n)).map (finPart D) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have gen : ∀ s : G D n, ((∃ b, mat s = blk4 1 b 0 1) ∨ (∃ a d, mat s = blk4 a 0 0 d) ∨ (∃ c, mat s = blk4 1 0 c 1)) →
      IsTrivAt θ τ (π s) ∧ ((∃ b, mat (π s) = blk4 1 b 0 1) ∨ (∃ a d, mat (π s) = blk4 a 0 0 d) ∨
        (∃ c, mat (π s) = blk4 1 0 c 1)) := by
    intro s hs
    refine ⟨(hπ s).1, ?_⟩
    have e := (hπ s).2.1
    have hps : π s = s * (ι (yf s))⁻¹ := eq_mul_inv_of_mul_eq e.symm
    have hMaway : ∀ τ', τ' ≠ τ → compAt θ τ' (mat (ι (yf s))) = 1 := fun τ' h => (hι.2 (yf s)).2.1 τ' h
    have hMf : (mat (ι (yf s))).map (finPart D) = 1 := (hι.2 (yf s)).2.2
    have hMτ : compAt θ τ (mat (ι (yf s))) = compAt θ τ (mat s) := by
      have : compAt θ τ (mat s) = compAt θ τ (mat (π s)) * compAt θ τ (mat (ι (yf s))) := by
        conv_lhs => rw [e]
        rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, compAt_mul']
      rw [this, (hπ s).1, Matrix.one_mul]
    have hmat : mat (π s) = mat s * mat (ι (yf s))⁻¹ := by rw [hps, GlobalTheory.StdUnn.LeftInvSect.mat_mul]
    rcases hs with ⟨b, hb⟩ | ⟨a, d, had⟩ | ⟨c, hc⟩
    · rw [hb, component_block_matrix, compAt_one', compAt_zero'] at hMτ
      obtain ⟨A, B, C, E', hM, hA, -, hC, hE, haw, hAf, -, hCf, hEf⟩ := blocks_of_away hθ hMaway hMf hMτ
      have hA1 : A = 1 := eq_of_comps hθ (by rw [hA, compAt_one']) (fun τ' h => by rw [(haw τ' h).1, compAt_one'])
        (by rw [hAf, fo])
      have hC0 : C = 0 := eq_of_comps hθ (by rw [hC, compAt_zero']) (fun τ' h => by rw [(haw τ' h).2.2.1, compAt_zero'])
        (by rw [hCf, fz])
      have hE1 : E' = 1 := eq_of_comps hθ (by rw [hE, compAt_one']) (fun τ' h => by rw [(haw τ' h).2.2.2, compAt_one'])
        (by rw [hEf, fo])
      rw [hA1, hC0, hE1] at hM
      refine Or.inl ⟨-adj B + b, ?_⟩
      rw [hmat, GlobalTheory.CompanionTheory.SwUnf.SmallCell.mat_inv _ hM, hb, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]
      congr 1 <;> simp [adj_one, adj_zero]
    · rw [had, component_block_matrix, compAt_zero'] at hMτ
      obtain ⟨A, B, C, E', hM, -, hB, hC, -, haw, -, hBf, hCf, -⟩ := blocks_of_away hθ hMaway hMf hMτ
      have hB0 : B = 0 := eq_of_comps hθ (by rw [hB, compAt_zero']) (fun τ' h => by rw [(haw τ' h).2.1, compAt_zero'])
        (by rw [hBf, fz])
      have hC0 : C = 0 := eq_of_comps hθ (by rw [hC, compAt_zero']) (fun τ' h => by rw [(haw τ' h).2.2.1, compAt_zero'])
        (by rw [hCf, fz])
      rw [hB0, hC0] at hM
      refine Or.inr (Or.inl ⟨a * adj E', d * adj A, ?_⟩)
      rw [hmat, GlobalTheory.CompanionTheory.SwUnf.SmallCell.mat_inv _ hM, had, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]
      congr 1 <;> simp [adj_zero]
    · rw [hc, component_block_matrix, compAt_one', compAt_zero'] at hMτ
      obtain ⟨A, B, C, E', hM, hA, hB, -, hE, haw, hAf, hBf, -, hEf⟩ := blocks_of_away hθ hMaway hMf hMτ
      have hA1 : A = 1 := eq_of_comps hθ (by rw [hA, compAt_one']) (fun τ' h => by rw [(haw τ' h).1, compAt_one'])
        (by rw [hAf, fo])
      have hB0 : B = 0 := eq_of_comps hθ (by rw [hB, compAt_zero']) (fun τ' h => by rw [(haw τ' h).2.1, compAt_zero'])
        (by rw [hBf, fz])
      have hE1 : E' = 1 := eq_of_comps hθ (by rw [hE, compAt_one']) (fun τ' h => by rw [(haw τ' h).2.2.2, compAt_one'])
        (by rw [hEf, fo])
      rw [hA1, hB0, hE1] at hM
      refine Or.inr (Or.inr ⟨c + -adj C, ?_⟩)
      rw [hmat, GlobalTheory.CompanionTheory.SwUnf.SmallCell.mat_inv _ hM, hc, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]
      congr 1 <;> simp [adj_one, adj_zero]
  set S : Set (G D n) := {g | (∃ b, mat g = blk4 1 b 0 1) ∨ (∃ a d, mat g = blk4 a 0 0 d) ∨ (∃ c, mat g = blk4 1 0 c 1)}
    with hSdef
  have hxS : x ∈ Submonoid.closure (S ∪ S⁻¹) := by
    rw [← Subgroup.closure_toSubmonoid, hG D n]
    show x ∈ (⊤ : Subgroup (G D n))
    exact Subgroup.mem_top x
  have key : ∀ g ∈ Submonoid.closure (S ∪ S⁻¹), π g ∈ Submonoid.closure {x : G D n | IsTrivAt θ τ x ∧
      ((∃ b, mat x = blk4 1 b 0 1) ∨ (∃ a d, mat x = blk4 a 0 0 d) ∨ (∃ c, mat x = blk4 1 0 c 1))} := by
    intro g hg
    induction hg using Submonoid.closure_induction with
    | mem g hg =>
      apply Submonoid.subset_closure
      rcases hg with hg | hg
      · exact gen g hg
      · exact gen g (gens_inv g hg)
    | one => rw [πtriv 1 triv_one]; exact one_mem _
    | mul g h _ _ ihg ihh => rw [πmul]; exact mul_mem ihg ihh
  have := key x hxS
  rwa [πtriv x hx] at this

end PositivityTheory.Rg.Sw.Glob.AW
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.CompAtSubSIns
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open Formalism.IndefR.Eqv (psiT eq_thetaC mat_ext psiT_sigR finPart_sigR)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP
open Classical

variable {D : D7} {n m : ℕ}

set_option synthInstance.maxHeartbeats 400000 in
theorem compAt_sub_sIns {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ}
    (hdet : IsUnit fr.det) (y : Mx D m n) :
    (y - sIns τ fr (piF θ τ fr y)).map (psiT D τ) = 0 := by
  have hp : Matrix.of (piF θ τ fr y) = fr⁻¹ * compAt θ τ y := rfl
  rw [Matrix.map_sub (psiT D τ) (fun a b => map_sub (psiT D τ) a b), ← PlaceFactsH.compAt_eq_psiT hθ,
    ← PlaceFactsH.compAt_eq_psiT hθ, show sIns (D := D) τ fr (piF θ τ fr y) = insT τ (fr * Matrix.of (piF θ τ fr y)) from rfl,
    compAt_insT hθ, if_pos rfl, hp, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul, sub_self]

set_option synthInstance.maxHeartbeats 400000 in

theorem inner_away {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau} (x x' z : Mx D V.rank n)
    (hx : ∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x') (hf : x.map (finPart D) = x'.map (finPart D))
    (hz : z.map (psiT D τ) = 0) : inner V x z = inner V x' z := by
  apply mat_ext D
  · intro τ''
    rw [map_inner, map_inner]
    by_cases h : τ'' = τ
    · subst h; rw [hz, Matrix.mul_zero, Matrix.mul_zero, Matrix.mul_zero]
    · have := hx τ'' h
      rw [eq_thetaC D hθ] at this
      change x.map (psiT D τ'') = x'.map (psiT D τ'') at this
      rw [this]
  · have ha : (adj x).map (finPart D) = (adj x').map (finPart D) := by
      ext i j
      simp only [adj, Matrix.map_apply, Matrix.transpose_apply, cA]
      rw [finPart_sigR, finPart_sigR]
      congr 1
      exact congrFun (congrFun hf j) i
    show (adj x * (gA V * z)).map (finPart D) = (adj x' * (gA V * z)).map (finPart D)
    rw [Matrix.map_mul, ha, ← Matrix.map_mul]

end PositivityTheory.Rg.Sw.Glob.FTH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocKvac
section
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn MvPolynomial
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 8000000

open RhoH in
theorem lIkvac : LIkvac := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL e hvac k hk
  classical
  obtain ⟨𝓕, hμ⟩ := hC.hμ
  have hΨ0m : psi0 θ V n l s τ ∈ awayA θ V n l s τ := unitaryFinitePointsToGLFiniteAdeles_isUnitary θ V l s τ
  have hl0 : ∀ τ, l τ ≠ 0 := l_ne_zero D n V ψ hC.hψ χ hC.hχ hC.hη θ hC.hθ μ 𝓕 hμ ω hC.hω l hC.hl
  have hmem : ∀ P : PX V.rank n, tens θ τ fr (fP (cLoc l τ) P) (psi0 θ V n l s τ) ∈ schwartzA θ V.rank n ∧
      tens θ τ fr (fP (cLoc l τ) P) (psi0 θ V n l s τ) ∈ fockA θ V n l s :=
    fun P => hT D n V θ l s τ ε fr hC.hθ hl0 hC.hs hC.hfr _ hΨ0m P
  have hM : ∀ τ, (gramAt D V τ * s τ).IsHermitian := fun τ => (hC.hs τ).2.2.1

  have hann1 : ∀ X, annS V l s θ τ X (phiS θ τ fr (cLoc l τ) (psi0 θ V n l s τ) 1).1 = 0 := by
    intro X
    rw [phiS_val (hmem 1).1]
    funext x
    rw [annS_tens hC.hθ hC.hfr hM l]
    simp
  have hann2 := annS_stable D n V ψ hC.hψ χ hC.hχ hC.hη θ hC.hθ μ 𝓕 hμ ω hC.hω l hC.hl s hC.hs τ _ hann1 (ι k)
    (iota_mem_K hC.hθ hC.hι k hk)
  rw [hL k _ hΨ0m 1] at hann2

  have hΦ : (phiS θ τ fr (cLoc l τ) (psi0 θ V n l s τ) 1).1 ∈ fockA θ V n l s := by
    rw [phiS_val (hmem 1).1]
    exact (hmem 1).2
  have hst := fock_stable D n V ψ hC.hψ χ hC.hχ hC.hη θ hC.hθ μ 𝓕 hμ ω hC.hω l hC.hl s hC.hs _ hΦ (ι k)
    (iota_mem_K hC.hθ hC.hι k hk)
  rw [hL k _ hΨ0m 1] at hst
  obtain ⟨Q, hQ⟩ := tens_slice hC.hθ hC.hfr l _ hst
  rw [hQ] at hann2
  have hQc := const_of_annS hC.hθ hC.hfr hM l Q hann2
  set a := evX Q 0 with ha
  have hL1 : L k (fP (cLoc l τ) 1) = a • fP (cLoc l τ) 1 := by
    rw [hQ, hQc]
    funext u
    simp [fP, evX]

  have hv := hvac k
  unfold sLd at hv
  rw [hL1] at hv
  have hg0 : gs (cLoc l τ) (0 : Fin V.rank → Fin n → ℂ) = 1 := by
    simp [gs]
  have hf0 : fP (cLoc l τ) (1 : PX V.rank n) 0 = 1 := by
    simp [fP, evX, hg0]
  simp only [Pi.smul_apply, smul_eq_mul, hf0, mul_one] at hv
  rw [hL1, hv]

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLaw
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocLawH

variable {D : D7} {n : ℕ}

theorem cnt_add {m : ℕ} (ε : Fin m → Bool) : cnt ε true + cnt ε false = m := by
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (fun a => ε a = true)
  simp only [Finset.card_univ, Fintype.card_fin, Bool.not_eq_true] at this
  exact this

theorem pqOf_add {m : ℕ} (ε : Fin m → Bool) (l : D.what₂.Tau → ℝ) (τ : D.what₂.Tau) :
    (pqOf ε l τ).1 + (pqOf ε l τ).2 = m := by
  unfold pqOf
  split_ifs
  · exact cnt_add ε
  · rw [add_comm]; exact cnt_add ε

theorem npow_sq (z : ℂ) (m : ℕ) : npow (‖z‖₊ ^ 2) ((m : ℂ) / 2) = ((‖z‖ : ℝ) : ℂ) ^ (m : ℤ) := by
  simp only [npow, NNReal.coe_pow, coe_nnnorm]
  rw [show ((m : ℂ) / 2) = (((m : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (sq_nonneg _), ← Real.rpow_natCast ‖z‖ 2, ← Real.rpow_mul (norm_nonneg _),
    show ((2 : ℕ) : ℝ) * ((m : ℝ) / 2) = (m : ℝ) by push_cast; ring, Real.rpow_natCast, zpow_natCast,
    Complex.ofReal_pow]

set_option maxHeartbeats 400000 in
theorem scal {χ : (AE D)ˣ →* Circle} {θ : InfFam D} (hθ : IsInfFam θ) {σ : (D.what₂.Tau → ℂ) →+ AE D}
    (hσ : GlobalTheory.FockCompare.Chart θ σ) {τ : D.what₂.Tau} {m : ℕ} (k j : ℤ)
    (hk : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → (∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1) →
      ((χ x : Circle) : ℂ) = (θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ)) ^ k)
    (hj : k - m = j + j) (p q : ℕ) (hpq : p + q = m) (y : PositivityTheory.Rg.Sw.GR n) (hy : (mR y).toBlocks₂₁ = 0) :
    (χ (Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) : ℂ) *
      npow (absA D (Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy)))) ((m : ℂ) / 2) = F0 p q (k - j) y := by
  have hv : (unitAt hσ τ (aOf y hy)).1 = baseColumnsAt σ τ (mR y).toBlocks₁₁ := by rw [unitAt_val, aOf_val]
  have hxv : ((Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy)) : (AE D)ˣ) : AE D) =
      (baseColumnsAt σ τ (mR y).toBlocks₁₁).det := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hv]
  have hf : finPart D (((Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) : (AE D)ˣ) : AE D) = 1 := by
    rw [hxv, RingHom.map_det, RingHom.mapMatrix_apply, finite_part_adelic_point_matrix hσ, Matrix.det_one]
  have hcomp : ∀ τ', θ τ' (infPart D (((Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) : (AE D)ˣ) : AE D)) = (compAt θ τ' (baseColumnsAt σ τ (mR y).toBlocks₁₁)).det := by
    intro τ'
    rw [hxv]
    show cf θ τ' (baseColumnsAt σ τ (mR y).toBlocks₁₁).det = _
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    rfl
  have hτ : θ τ (infPart D (((Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) : (AE D)ˣ) : AE D)) = ((mR y).toBlocks₁₁).det := by rw [hcomp, component_adelic_point_matrix hσ]
  have hne : ∀ τ', τ' ≠ τ → θ τ' (infPart D (((Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) : (AE D)ˣ) : AE D)) = 1 := fun τ' h => by
    rw [hcomp, component_adelic_point_ne hσ h, Matrix.det_one]
  have habs : absA D (Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) = ‖((mR y).toBlocks₁₁).det‖₊ ^ 2 := by
    rw [show absA D (Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) = ‖θ τ (infPart D (((Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) : (AE D)ˣ) : AE D))‖₊ ^ 2 from GlobalTheory.StabAtPlace.absE_single hθ (Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) τ hf hne, hτ]
  rw [hk _ hf hne, hτ, habs, npow_sq]
  have hZ := det_ne y hy
  have hu1 : u1 (mR y) = (mR y).toBlocks₂₂ := by simp only [u1, hy, smul_zero, zero_add]
  have hu2 : u2 (mR y) = (mR y).toBlocks₂₂ := by simp only [u2, hy, smul_zero, neg_zero, zero_add]
  have hdy : (mR y).det = ((mR y).toBlocks₁₁).det * ((mR y).toBlocks₂₂).det := by
    conv_lhs => rw [fromBlocks_of y hy]
    rw [Matrix.det_fromBlocks_zero₂₁]
  have hR : ((‖((mR y).toBlocks₁₁).det‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hZ)
  have hd : ((mR y).toBlocks₂₂).det = ((mR y).toBlocks₁₁).det / ((‖((mR y).toBlocks₁₁).det‖ : ℝ) : ℂ) ^ 2 := by
    have h1 : ((mR y).toBlocks₂₂).det = (star ((mR y).toBlocks₁₁).det)⁻¹ := eq_inv_of_mul_eq_one_right (det_rel y hy)
    have h2 : ((mR y).toBlocks₁₁).det * star ((mR y).toBlocks₁₁).det = ((‖((mR y).toBlocks₁₁).det‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    have h3 : star ((mR y).toBlocks₁₁).det ≠ 0 := star_ne_zero.2 hZ
    rw [h1, eq_div_iff (pow_ne_zero 2 hR), ← h2]
    field_simp
  simp only [F0, f0, hu1, hu2, hdy, hd]
  exact alg_id _ _ hZ hR k j p q m hpq hj

end PositivityTheory.Rg.Sw.Glob.LocLawH

namespace PositivityTheory.Rg.Sw.Glob

theorem lIlaw : LIlaw := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hC.hθ
  obtain ⟨k, ⟨j, hj⟩, hk⟩ := LocLawH.chi_exp hC.hθ hC.hχ hC.hη τ
  exact ⟨k - j, fun P y g hy => by
    rw [LocLawH.glob_law hC hL hσ P y g hy, LocLawH.scal hC.hθ hσ k j hk hj _ _ (LocLawH.pqOf_add ε l τ) y hy]⟩

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.MatLApply
section
noncomputable section

open Filter Topology MvPolynomial Set
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.Glob.SchDH

variable {m n : ℕ}

def matLin (M : Matrix (Fin m) (Fin m) ℂ) : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) where
  toFun y := fun a i => ∑ c, M a c * y c i
  map_add' y z := by funext a i; simp [mul_add, Finset.sum_add_distrib]
  map_smul' r y := by
    funext a i
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Complex.real_smul, Complex.real_smul]; ring

def matL (M : Matrix (Fin m) (Fin m) ℂ) : (Fin m → Fin n → ℂ) →L[ℝ] (Fin m → Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap (matLin M)

theorem matL_apply (M : Matrix (Fin m) (Fin m) ℂ) (y : Fin m → Fin n → ℂ) (a : Fin m) (i : Fin n) :
    matL M y a i = ∑ c, M a c * y c i := rfl

theorem matL_mul (M N : Matrix (Fin m) (Fin m) ℂ) (y : Fin m → Fin n → ℂ) : matL (M * N) y = matL M (matL N y) := by
  funext a i
  simp only [matL_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem matL_one (y : Fin m → Fin n → ℂ) : matL (1 : Matrix (Fin m) (Fin m) ℂ) y = y := by
  funext a i
  simp [matL_apply, Matrix.one_apply]

theorem contDiff_A (X : Matrix (Fin m) (Fin m) ℂ) :
    ContDiff ℝ ∞ (fun t : ℝ => matL (n := n) (NormedSpace.exp ((t : ℂ) • X))) := by
  letI : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedSpace
  letI : NormedRing (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAlgebra
  let Lm : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] ((Fin m → Fin n → ℂ) →L[ℝ] (Fin m → Fin n → ℂ)) :=
    { toFun := matL
      map_add' := fun M N => by ext y a i; simp [matL_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r M => by
        ext y a i
        simp only [matL_apply, Matrix.smul_apply, RingHom.id_apply, ContinuousLinearMap.smul_apply, Pi.smul_apply,
          Finset.smul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Complex.real_smul, Complex.real_smul]; ring }
  have hexp : ContDiff ℝ ∞ (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) := by
    have e : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) = NormedSpace.exp ∘ (fun t : ℝ => t • X) := by
      funext t; simp only [Function.comp_apply, Complex.coe_smul]
    rw [e]
    exact (contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt).comp
      (contDiff_id.smul contDiff_const)
  exact (LinearMap.toContinuousLinearMap Lm).contDiff.comp hexp

theorem hasDerivAt_entry (X : Matrix (Fin m) (Fin m) ℂ) (a c : Fin m) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) a c) (X a c) 0 := by
  letI : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedSpace
  letI : NormedRing (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAlgebra
  let ent : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M a c, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ))
  have h2 := (LinearMap.toContinuousLinearMap ent).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have e : (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) a c) =
      (LinearMap.toContinuousLinearMap ent) ∘ (fun u : ℝ => NormedSpace.exp (u • X)) := by
    funext t; simp only [Function.comp_apply, Complex.coe_smul]; rfl
  have h3 : HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) a c)
      ((LinearMap.toContinuousLinearMap ent) (NormedSpace.exp ((0 : ℝ) • X) * X)) 0 := by
    rw [e]; exact h2
  have h4 : (LinearMap.toContinuousLinearMap ent) (NormedSpace.exp ((0 : ℝ) • X) * X) = X a c := by
    rw [zero_smul, NormedSpace.exp_zero, one_mul]; rfl
  rw [h4] at h3
  exact h3

theorem exists_gs (c : ℝ) (hc : 0 < c) : ∃ g : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∀ u, g u = gs c u := by
  obtain ⟨g0, hg0⟩ := GlobalTheory.CompanionTheory.PolyGaussSchwartz.exists_gauss (m := m) (n := n)
  set s : ℝ := Real.sqrt (c / (2 * Real.pi)) with hs
  have hs0 : s ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  let L : (Fin m → Fin n → ℂ) ≃L[ℝ] (Fin m → Fin n → ℂ) :=
    (LinearEquiv.smulOfNeZero ℝ (Fin m → Fin n → ℂ) s hs0).toContinuousLinearEquiv
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L g0, fun u => ?_⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hg0]
  have key : 2 * Real.pi * ∑ a, ∑ i, ‖(L u) a i‖ ^ 2 = c * ∑ a, ∑ i, ‖u a i‖ ^ 2 := by
    have h1 : ∀ a i, ‖(L u) a i‖ ^ 2 = s ^ 2 * ‖u a i‖ ^ 2 := fun a i => by
      change ‖(s • u) a i‖ ^ 2 = _
      rw [Pi.smul_apply, Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    simp only [h1, ← Finset.mul_sum]
    rw [hs, Real.sq_sqrt (by positivity)]
    field_simp
  unfold gs
  rw [key]

theorem exists_fP (c : ℝ) (hc : 0 < c) (P : PX m n) :
    ∃ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∀ u, φ u = fP c P u := by
  obtain ⟨g, hg⟩ := exists_gs (m := m) (n := n) c hc
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun u => MvPolynomial.eval (fun k => GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord k u) P) g,
    fun u => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply (GlobalTheory.CompanionTheory.PolyGaussSchwartz.eval_temperate P), hg, smul_eq_mul]
  rfl

end PositivityTheory.Rg.Sw.Glob.SchDH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WopTop
section
namespace PositivityTheory.Rg.Sw.Glob

theorem opGen_of (hF : FTfact) : OpGen := opGen_of' unipTau leviTau wEx schOps hF

theorem opCLM_of' (hF : FTfact) : OpCLM := opCLM_of unipTau leviTau wEx schOps hF decomp lNe

theorem local_L2_isometry (hF : FTfact) : LocalL2Isometry :=
  local_isometry_of_hypotheses unipTau leviTau wEx schOps hF decomp lNe planchLoc awayNZ

end PositivityTheory.Rg.Sw.Glob
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Wtc
section
namespace PositivityTheory.Rg.Sw.Glob

theorem wtc : GlobalTheory.Published.WeilThetaConvergence := GlobalTheory.CompanionTheory.WTC.weilThetaConvergence_of_core GlobalTheory.CompanionTheory.SiegelRed.siegelCore

end PositivityTheory.Rg.Sw.Glob
end

