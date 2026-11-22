import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InputExistsOfMemberExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0944
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0977
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0972
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0042
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0973

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermFormReindex
section
open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameEquiv.Reindex

attribute [local instance] Over.cartesianMonoidalCategory

variable {g g' : ℕ}

noncomputable def rho (ε : Fin g' ≃ Fin g) : (Fin g → ℂ) →L[ℂ] (Fin g' → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (ε i)

theorem rho_apply (ε : Fin g' ≃ Fin g) (z : Fin g → ℂ) : rho ε z = z ∘ ε := rfl

theorem rho_single (ε : Fin g' ≃ Fin g) (m : Fin g) : rho ε (Pi.single m 1) = Pi.single (ε.symm m) 1 := by
  funext i
  rw [rho_apply, Function.comp_apply, Pi.single_apply, Pi.single_apply]
  simp only [Equiv.eq_symm_apply]

theorem rho_injective (ε : Fin g' ≃ Fin g) : Function.Injective (rho ε) := fun z w h => by
  funext i
  simpa [rho_apply] using congrFun h (ε.symm i)

theorem hermForm_reindex (ε : Fin g' ≃ Fin g) (Hm : Matrix (Fin g') (Fin g') ℂ) (z w : Fin g → ℂ) :
    hermForm (Hm.submatrix ε.symm ε.symm) z w = hermForm Hm (rho ε z) (rho ε w) := by
  unfold hermForm
  rw [Matrix.submatrix_mulVec_equiv, Equiv.symm_symm, dotProduct_comp_equiv_symm]
  rfl

noncomputable def rhoM (ε : Fin g' ≃ Fin g) : (Fin g → ℂ) ≃ᵐ (Fin g' → ℂ) :=
  (MeasurableEquiv.piCongrLeft (fun _ => ℂ) ε).symm

theorem rhoM_eq (ε : Fin g' ≃ Fin g) : ⇑(rhoM ε) = ⇑(rho ε) := rfl

theorem rho_mp (ε : Fin g' ≃ Fin g) : MeasurePreserving (rhoM ε) volume volume :=
  (volume_measurePreserving_piCongrLeft (fun _ => ℂ) ε).symm _

theorem fund_reindex (ε : Fin g' ≃ Fin g) {A A' : Type} [AddCommGroup A] [AddCommGroup A'] (ψ : A ≃ A')
    (P : A →+ (Fin g → ℂ)) (P' : A' →+ (Fin g' → ℂ)) (h : ∀ a, P' (ψ a) = rho ε (P a)) {Fd : Set (Fin g' → ℂ)}
    (hF : IsAddFundamentalDomain P'.range Fd volume) : IsAddFundamentalDomain P.range (rho ε ⁻¹' Fd) volume := by
  have key : ∀ v : P'.range, rho ε.symm v.1 ∈ P.range := by
    rintro ⟨_, b, rfl⟩
    refine ⟨ψ.symm b, rho_injective ε ?_⟩
    rw [← h, Equiv.apply_symm_apply]
    funext i
    simp [rho_apply]
  refine hF.preimage_of_equiv (f := rho ε) (rho_mp ε).quasiMeasurePreserving
    (e := fun v => ⟨rho ε.symm v.1, key v⟩) ⟨fun v w hvw => ?_, ?_⟩ fun v z => ?_
  · exact Subtype.ext (rho_injective _ (congrArg Subtype.val hvw))
  · rintro ⟨_, a, rfl⟩
    refine ⟨⟨P' (ψ a), ψ a, rfl⟩, Subtype.ext ?_⟩
    funext i
    simp [h, rho_apply]
  · funext i
    change v.1 (ε.symm (ε i)) + z (ε i) = v.1 i + z (ε i)
    rw [Equiv.symm_apply_apply]

open MonObj in
theorem left_eq {S : Scheme.{0}} {G : Over S} [GrpObj G] {y y' : Sp ℂ ⟶ S} (hy : y = y')
    (ρ : (Fin g → ℂ) →L[ℂ] (Fin g' → ℂ))
    {e : (Fin g → ℂ) → (Over.mk y ⟶ G)} {e' : (Fin g' → ℂ) → (Over.mk y' ⟶ G)}
    (he : ∀ z w, e (z + w) = e z * e w) (he' : ∀ z w, e' (z + w) = e' z * e' w)
    (hol : IsHolTo Set.univ (fun z => (e z).left)) (hol' : IsHolTo Set.univ (fun z => (e' z).left))
    (u : Fin g → (Sp (DualNumber ℂ) ⟶ G.left)) (hd : ∀ i, IsDerivAt0 (fun z => (e z).left) (Pi.single i 1) (u i))
    (hd' : ∀ i, IsDerivAt0 (fun z => (e' z).left) (ρ (Pi.single i 1)) (u i)) (z : Fin g → ℂ) :
    (e z).left = (e' (ρ z)).left := by
  subst hy
  have E : e = fun z => e' (ρ z) :=
    GlobalTheory.CuspFamilyCompare.exp_unique he (fun z w => by rw [map_add, he']) hol
      (HolHom.isHolTo_of_holAt isOpen_univ fun z _ =>
        (HolHom.holAt_of_isHolTo hol' (Set.mem_univ (ρ z))).precomp ρ.differentiableAt)
      u hd (fun m => GlobalTheory.CuspFamilyCompare.isDerivAt0_comp hol' ρ (hd' m))
  rw [E]

end GlobalTheory.FrameEquiv.Reindex

namespace GlobalTheory.FrameEquiv

open Reindex

set_option maxHeartbeats 1000000 in

theorem hasWitness_of_is : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → ∀ (W : HSp D) (hr : W.rank = r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (d : GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws.DictDat U), d.Is W hr dict ι x₀ → HasWitness d := by
  intro D H Dw l Xo c σ r U _ hU _ W hr dict ι x₀ d hd
  obtain ⟨W₀⟩ := nonempty_uw ((Formalism.L2.PjFree.isUnf_ofPj U).2 hU)
  obtain ⟨-, ⟨hiso, hpt⟩, -⟩ := hd
  refine ⟨⟨d.g, d.e, d.F, d.ik, d.φ, hiso, fun k x => ?_⟩, rfl⟩
  obtain ⟨Pm, h1, h2, h3, h4⟩ := hpt k x
  refine ⟨Pm, h1, h2, h3, h4, fun hun => ?_⟩
  obtain ⟨Pm', b1, b2, b3, b4, b5⟩ := W₀.pt k x
  obtain ⟨Hm, χl, fr, θ, Fd, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11⟩ := b5 hun
  let ε : Fin W₀.g ≃ Fin d.g := W₀.e.trans d.e.symm
  let ψ : (d.F.Di (d.ik k)).La ≃ (W₀.F.Di (W₀.ik k)).La := ((d.φ k).trans (W₀.φ k).symm).toEquiv
  have hψ : ∀ a, W₀.φ k (ψ a) = d.φ k a := fun a => (W₀.φ k).apply_symm_apply _
  have hP : ∀ a, Pm' (ψ a) = rho ε (Pm a) := fun a => by
    funext j
    have hj : d.e (ε j) = W₀.e j := d.e.apply_symm_apply _
    rw [rho_apply, Function.comp_apply, h1, b1, hψ, hj]
    rfl
  have hE : ∀ z, (d.F.ex (d.ik k) Pm z).left = (W₀.F.ex (W₀.ik k) Pm' (rho ε z)).left :=
    left_eq (h3.symm.trans b3) (rho ε) (d.F.ex_add _ _ h2) (W₀.F.ex_add _ _ b2)
      (GlobalTheory.CuspFamilyCompare.isHolTo_ex _ _ h2) (GlobalTheory.CuspFamilyCompare.isHolTo_ex _ _ b2)
      (fun m => (U.un k x).u (d.e m).1 (d.e m).2)
      (fun m => by simpa using h4 (d.e m).1 (d.e m).2)
      (fun m => by rw [rho_single]; exact b4 (d.e m).1 (d.e m).2)
  refine ⟨Hm.submatrix ε.symm ε.symm, fun z => χl (rho ε z), fun j z => fr j (rho ε z), fun z => θ (rho ε z),
    rho ε ⁻¹' Fd, c1.submatrix _, fun z hz => ?_, fun a b => ?_, fun j => ?_, fun j z hz => ?_, fun j j' z hz => ?_,
    fun j hz => ?_, fun a j z => ?_, fun j z pt p1 p2 hz => ?_, fund_reindex ε ψ Pm Pm' hP c10, ?_⟩
  · rw [hermForm_reindex]
    exact c2 _ fun h0 => hz (rho_injective ε (h0.trans (map_zero _).symm))
  · rw [hermForm_reindex, ← hP, ← hP, c3]
    have := (W₀.isom k (ψ a) (ψ b))
    rw [hψ, hψ] at this
    exact_mod_cast this.trans (hiso k a b).symm
  · refine (c4 j).comp (rho ε).differentiable.differentiableOn fun z hz => ?_
    rw [Set.mem_ofPred_eq, hE] at hz
    exact hz
  · rw [hE] at hz
    exact c5 _ _ hz
  · rw [hE] at hz ⊢
    exact c6 _ _ _ hz
  · rw [hE, map_zero] at hz
    simp only [map_zero]
    exact c7 _ hz
  · simp only [hermForm_reindex, map_add, ← hP, hE]
    exact c8 _ _ _
  · rw [hE] at hz p1
    exact c9 _ _ _ p1 p2 hz
  · simp only [hermForm_reindex]
    have m1 : volume (rho ε ⁻¹' Fd) = volume Fd := (rho_mp ε).measure_preimage_equiv Fd
    have m2 := (rho_mp ε).setIntegral_preimage_emb (rhoM ε).measurableEmbedding
      (fun z => ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) Fd
    rw [m1]
    exact (congrArg (· / _) m2).trans c11

end GlobalTheory.FrameEquiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianCongrOfPositiveIndexEq
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.HermCongruence

def signVec {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) : Fin n → ℂ :=
  fun i => if 0 < hA.eigenvalues i then 1 else -1

theorem eigenvalues_ne_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hd : A.det ≠ 0)
    (i : Fin n) : hA.eigenvalues i ≠ 0 := by
  intro h
  apply hd
  rw [hA.det_eq_prod_eigenvalues]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h])

theorem exists_congr_signVec {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hd : A.det ≠ 0) :
    ∃ V : GL (Fin n) ℂ, (V : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * V = diagonal (signVec hA) := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hUU : Uᴴ * U = 1 := by
    have := hA.eigenvectorUnitary.2.1
    simpa [hU, Matrix.star_eq_conjTranspose] using this
  have hspec : A = U * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have := hA.spectral_theorem
    simpa [hU, Matrix.star_eq_conjTranspose, Function.comp_def] using this
  set c : Fin n → ℂ := fun i => ((Real.sqrt |hA.eigenvalues i|)⁻¹ : ℝ) with hc
  have hc0 : ∀ i, c i ≠ 0 := by
    intro i
    have h1 : 0 < |hA.eigenvalues i| := abs_pos.2 (eigenvalues_ne_zero hA hd i)
    simp [hc, Real.sqrt_eq_zero', not_le.2 h1, eigenvalues_ne_zero hA hd i]
  set V := U * diagonal c with hV
  have hVdet : V.det ≠ 0 := by
    rw [hV, det_mul, det_diagonal]
    refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.2 fun i _ => hc0 i)
    intro h
    have := congrArg det hUU
    rw [det_mul, h, mul_zero, det_one] at this
    exact zero_ne_one this
  refine ⟨GeneralLinearGroup.mkOfDetNeZero V hVdet, ?_⟩
  show Vᴴ * A * V = _
  have hcs : (diagonal c)ᴴ = diagonal c := by
    rw [diagonal_conjTranspose]
    congr 1; funext i; simp [hc]
  rw [hV, conjTranspose_mul, hcs]
  conv_lhs => rw [hspec]
  have : diagonal c * Uᴴ * (U * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * Uᴴ) * (U * diagonal c) =
      diagonal c * (Uᴴ * U) * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * (Uᴴ * U) * diagonal c := by
    simp only [Matrix.mul_assoc]
  rw [this, hUU, Matrix.mul_one, Matrix.mul_one, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  have hne := eigenvalues_ne_zero hA hd i
  have hpos : 0 < |hA.eigenvalues i| := abs_pos.2 hne
  have hsq : Real.sqrt |hA.eigenvalues i| * Real.sqrt |hA.eigenvalues i| = |hA.eigenvalues i| :=
    Real.mul_self_sqrt hpos.le
  have hs0 : Real.sqrt |hA.eigenvalues i| ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  have key : (Real.sqrt |hA.eigenvalues i|)⁻¹ * hA.eigenvalues i * (Real.sqrt |hA.eigenvalues i|)⁻¹ =
      if 0 < hA.eigenvalues i then 1 else -1 := by
    rw [mul_comm, ← mul_assoc, ← mul_inv, hsq]
    split_ifs with h
    · rw [abs_of_pos h]; field_simp
    · rw [abs_of_neg (lt_of_le_of_ne (not_lt.1 h) hne)]; field_simp
  simp only [signVec, hc]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, key]
  split_ifs <;> simp

end GlobalTheory.HermCongruence

namespace GlobalTheory.HermCongruence

theorem exists_equiv_pos {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : sigPosH hA = sigPosH hB) :
    ∃ e : Fin n ≃ Fin n, ∀ i, (0 < hA.eigenvalues (e i) ↔ 0 < hB.eigenvalues i) := by
  have h1 : Fintype.card {i // 0 < hB.eigenvalues i} = Fintype.card {i // 0 < hA.eigenvalues i} := h.symm
  have h2 : Fintype.card {i // ¬ 0 < hB.eigenvalues i} = Fintype.card {i // ¬ 0 < hA.eigenvalues i} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h1]
  refine ⟨Equiv.subtypeCongr (Fintype.equivOfCardEq h1) (Fintype.equivOfCardEq h2), fun i => ?_⟩
  by_cases hi : 0 < hB.eigenvalues i
  · have hx : Equiv.subtypeCongr (Fintype.equivOfCardEq h1) (Fintype.equivOfCardEq h2) i =
        ((Fintype.equivOfCardEq h1) ⟨i, hi⟩ : Fin n) := by
      simp [Equiv.subtypeCongr, hi]
    rw [hx]
    exact iff_of_true ((Fintype.equivOfCardEq h1) ⟨i, hi⟩).2 hi
  · have hx : Equiv.subtypeCongr (Fintype.equivOfCardEq h1) (Fintype.equivOfCardEq h2) i =
        ((Fintype.equivOfCardEq h2) ⟨i, hi⟩ : Fin n) := by
      simp [Equiv.subtypeCongr, hi]
    rw [hx]
    exact iff_of_false ((Fintype.equivOfCardEq h2) ⟨i, hi⟩).2 hi

theorem perm_congr {n : ℕ} (d : Fin n → ℂ) (e : Fin n ≃ Fin n) :
    ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e)ᴴ * diagonal d * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e =
      diagonal (d ∘ e) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.one_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply]
  split_ifs with h <;> simp [h]

theorem congr_of_sigPosH_eq : ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian),
    A.det ≠ 0 → B.det ≠ 0 → sigPosH hA = sigPosH hB →
      ∃ Z : GL (Fin n) ℂ, B = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * (Z : Matrix (Fin n) (Fin n) ℂ) := by
  intro n A B hA hB hdA hdB hs
  obtain ⟨VA, hVA⟩ := exists_congr_signVec hA hdA
  obtain ⟨VB, hVB⟩ := exists_congr_signVec hB hdB
  obtain ⟨e, he⟩ := exists_equiv_pos hA hB hs
  set P : Matrix (Fin n) (Fin n) ℂ := (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e with hP
  have hPP : P * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e.symm = 1 := by
    ext i j; simp [hP, Matrix.mul_apply, Matrix.one_apply]
  have hPdet : P.det ≠ 0 := by
    intro h
    have := congrArg det hPP
    rw [det_mul, h, zero_mul, det_one] at this
    exact zero_ne_one this
  have hsig : signVec hA ∘ e = signVec hB := by
    funext i
    simp only [Function.comp_apply, signVec]
    by_cases hi : 0 < hB.eigenvalues i
    · rw [if_pos hi, if_pos ((he i).2 hi)]
    · rw [if_neg hi, if_neg (fun h => hi ((he i).1 h))]
  refine ⟨VA * GeneralLinearGroup.mkOfDetNeZero P hPdet * VB⁻¹, ?_⟩
  set W : Matrix (Fin n) (Fin n) ℂ := ((VB⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) with hW
  have hVW : (VB : Matrix (Fin n) (Fin n) ℂ) * W = 1 := by
    rw [hW, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hWV : Wᴴ * (VB : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 := by
    rw [← conjTranspose_mul, hVW, conjTranspose_one]
  have hP' : ((GeneralLinearGroup.mkOfDetNeZero P hPdet : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = P := rfl
  rw [Units.val_mul, Units.val_mul, hP', ← hW, conjTranspose_mul, conjTranspose_mul]
  have : Wᴴ * (Pᴴ * (VA : Matrix (Fin n) (Fin n) ℂ)ᴴ) * A * (VA * P * W) =
      Wᴴ * (Pᴴ * ((VA : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * VA) * P) * W := by
    simp only [Matrix.mul_assoc]
  rw [this, hVA, hP, perm_congr, hsig, ← hVB]
  have : Wᴴ * ((VB : Matrix (Fin n) (Fin n) ℂ)ᴴ * B * VB) * W =
      (Wᴴ * (VB : Matrix (Fin n) (Fin n) ℂ)ᴴ) * B * ((VB : Matrix (Fin n) (Fin n) ℂ) * W) := by
    simp only [Matrix.mul_assoc]
  rw [this, hWV, hVW, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.HermCongruence
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleFrobeniusTwistOrderFixedPoints
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.SigIter

variable {p : ℕ} [Fact p.Prime]

theorem iterate_fst (G : HTGroup p) (r k : ℕ) (g : Gr G r) :
    ((⇑(sigG G r))^[k] g).1 = (⇑(GlobalTheory.LKLoc.sig p (Q0 p) 1 r))^[k] g.1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl

theorem iterate_snd (G : HTGroup p) (r k : ℕ) (g : Gr G r) (i : Fin G.m) :
    ((⇑(sigG G r))^[k] g).2 i = (⇑(sigRes p (G.Fw i) G.n r))^[k] (g.2 i) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl

theorem unramifiedExtFrobeniusGL_one_iterate_degree (r : ℕ) (hr : 0 < r) (g : GL (Fin 1) (Qr p r)) :
    (⇑(GlobalTheory.LKLoc.sig p (Q0 p) 1 r))^[r] g = g := by
  have h : ∀ (k : ℕ) (i j : Fin 1), ((⇑(GlobalTheory.LKLoc.sig p (Q0 p) 1 r))^[k] g).val i j
      = (⇑(frobQ p r))^[k] (g.val i j) := by
    intro k i j
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      rfl
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [h, GlobalTheory.LKResNrmConj.frobQ_iterate_self p r hr]

theorem inclK_injective (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) :
    Function.Injective (inclK p K r) :=
  Algebra.TensorProduct.includeLeft_injective (S := ℚ_[p]) (algebraMap ℚ_[p] (Qr p r)).injective

theorem iterate_self (G : HTGroup p) (r : ℕ) (hr : 0 < r) (g : Gr G r) : (⇑(sigG G r))^[r] g = g := by
  refine Prod.ext ?_ (funext fun i => ?_)
  · rw [iterate_fst, unramifiedExtFrobeniusGL_one_iterate_degree r hr]
  · rw [iterate_snd, GlobalTheory.LKResNrmConj.sigRes_iterate_self p (G.Fw i) G.n r hr]

theorem fix_incl (G : HTGroup p) (r : ℕ) (γ : Gp G) : sigG G r (inclG G r γ) = inclG G r γ := by
  refine Prod.ext ?_ (funext fun i => ?_)
  · refine Units.ext (Matrix.ext fun a b => ?_)
    change frobQ p r (((inclG G r γ).1 : Matrix (Fin 1) (Fin 1) (Qr p r)) a b) = _
    simp only [inclG, MonoidHom.prodMap, MonoidHom.prod_apply, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.coe_fst, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.coe_map,
      MonoidHom.coe_coe]
    by_cases h : a = b
    · subst h; simp [Matrix.diagonal_apply_eq]
    · simp [Matrix.diagonal_apply_ne _ h]
  · refine Units.ext (Matrix.ext fun a b => ?_)
    change sigKQ p (G.Fw i) r (((inclG G r γ).2 i : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw i) r)) a b) = _
    simp only [inclG, MonoidHom.prodMap, MonoidHom.prod_apply, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.coe_snd, Pi.monoidHom_apply, Pi.evalMonoidHom_apply, GeneralLinearGroup.map_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    exact sigKQ_apply_inclK p (G.Fw i) r _

end GlobalTheory.LKMid.SigIter

namespace GlobalTheory.LKMid.SigIter

variable {p : ℕ} [Fact p.Prime]

theorem incl_injective (G : HTGroup p) (r : ℕ) : Function.Injective (inclG G r) := by
  intro γ γ' h
  have h1 := congrArg (fun g : Gr G r => ((g.1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0)) h
  have h2 := fun i (a b : Fin G.n) =>
    congrArg (fun g : Gr G r => ((g.2 i : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw i) r)) a b)) h
  simp only [inclG, MonoidHom.prodMap, MonoidHom.prod_apply, MonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.coe_fst, MonoidHom.coe_snd, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.coe_map,
    MonoidHom.coe_coe, Pi.monoidHom_apply, Pi.evalMonoidHom_apply, GeneralLinearGroup.map_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Matrix.diagonal_apply_eq] at h1 h2
  refine Prod.ext (Units.ext ((algebraMap ℚ_[p] (Qr p r)).injective h1)) (funext fun i => ?_)
  exact Units.ext (Matrix.ext fun a b => inclK_injective (G.Fw i) r (h2 i a b))

theorem fixed_mem_range (G : HTGroup p) (r : ℕ) (hr : 0 < r) (g : Gr G r) (hg : sigG G r g = g) :
    g ∈ (inclG G r).range := by
  have hf : frobQ p r ((g.1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0) = (g.1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0 :=
    congrArg (fun x : Gr G r => ((x.1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0)) hg
  obtain ⟨c, hc⟩ := frobQ_fixed_mem p r hr _ hf
  have hdet1 : IsUnit ((g.1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0) := by
    have := Matrix.isUnits_det_units g.1
    rwa [Matrix.det_fin_one] at this
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact not_isUnit_zero (hc ▸ hdet1)
  have hfix : ∀ i (a b : Fin G.n), ∃ x : G.Fw i,
      inclK p (G.Fw i) r x = (g.2 i : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw i) r)) a b := fun i a b =>
    sigKQ_fixed_eq_inclK p (G.Fw i) r hr _
      (congrArg (fun x : Gr G r => ((x.2 i : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw i) r)) a b)) hg)
  choose M hM using hfix
  have hmap : ∀ i, (Matrix.of (M i)).map (inclK p (G.Fw i) r) = (g.2 i : Matrix (Fin G.n) (Fin G.n) _) :=
    fun i => Matrix.ext fun a b => hM i a b
  have hdet : ∀ i, (Matrix.of (M i)).det ≠ 0 := by
    intro i h0
    have e := RingHom.map_det (inclK p (G.Fw i) r).toRingHom (Matrix.of (M i))
    rw [h0, map_zero, RingHom.mapMatrix_apply] at e
    have e' : (Matrix.of (M i)).map (inclK p (G.Fw i) r).toRingHom = (g.2 i : Matrix (Fin G.n) (Fin G.n) _) :=
      hmap i
    rw [e'] at e
    have hu := Matrix.isUnits_det_units (g.2 i)
    rw [← e] at hu
    have hsub : Subsingleton (KQ p (G.Fw i) r) := subsingleton_of_zero_eq_one (isUnit_zero_iff.1 hu)
    have := inclK_injective (G.Fw i) r (Subsingleton.elim (inclK p (G.Fw i) r 1) (inclK p (G.Fw i) r 0))
    exact one_ne_zero this
  refine ⟨(Units.mk0 c hc0, fun i => GeneralLinearGroup.mkOfDetNeZero (Matrix.of (M i)) (hdet i)), ?_⟩
  refine Prod.ext (Units.ext (Matrix.ext fun a b => ?_)) (funext fun i => Units.ext ?_)
  · have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha hb
    simp only [inclG, MonoidHom.prodMap, MonoidHom.prod_apply, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.coe_fst, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.coe_map,
      MonoidHom.coe_coe, Matrix.diagonal_apply_eq, Units.val_mk0]
    exact hc
  · rw [← hmap i]
    rfl

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r →
    (∀ g : Gr G r, (⇑(sigG G r))^[r] g = g) ∧ (∀ γ : Gp G, sigG G r (inclG G r γ) = inclG G r γ) ∧
      Function.Injective (inclG G r) ∧ ∀ g : Gr G r, sigG G r g = g → g ∈ (inclG G r).range :=
  fun _ _ G r hr => ⟨iterate_self G r hr, fix_incl G r, incl_injective G r, fixed_mem_range G r hr⟩

end GlobalTheory.LKMid.SigIter

example : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → (∀ g : Gr G r, (⇑(sigG G r))^[r] g = g) ∧ (∀ γ : Gp G, sigG G r (inclG G r γ) = inclG G r γ) ∧ Function.Injective (inclG G r) ∧ ∀ g : Gr G r, sigG G r g = g → g ∈ (inclG G r).range := GlobalTheory.LKMid.SigIter.main
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleTrivializationsDifferByGroupPoint
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem quot_mul_star {S A : Type*} [Ring S] [CommRing A] [Algebra A S] (σ : S →+* Sᵐᵒᵖ) (b : S) (x x' : Sˣ)
    (t t' : Aˣ) (hx : (x : S) * b * (σ x).unop = algebraMap A S t)
    (hx' : (x' : S) * b * (σ x').unop = algebraMap A S t') :
    ((x' * x⁻¹ : Sˣ) : S) * (σ ((x' * x⁻¹ : Sˣ) : S)).unop = algebraMap A S ((t' * t⁻¹ : Aˣ) : A) := by
  have h1 : (σ x).unop * (σ ((x⁻¹ : Sˣ) : S)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have ht : algebraMap A S ((t⁻¹ : Aˣ) : A) * algebraMap A S (t : A) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have h2 : ((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop = algebraMap A S ((t⁻¹ : Aˣ) : A) * b := by
    calc ((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop
        = algebraMap A S ((t⁻¹ : Aˣ) : A) * (((x⁻¹ : Sˣ) : S) * algebraMap A S (t : A) *
            (σ ((x⁻¹ : Sˣ) : S)).unop) := by
          rw [← Algebra.commutes (t : A), ← mul_assoc, ← mul_assoc, ht, one_mul]
      _ = algebraMap A S ((t⁻¹ : Aˣ) : A) * ((((x⁻¹ : Sˣ) : S) * x) * b *
            ((σ x).unop * (σ ((x⁻¹ : Sˣ) : S)).unop)) := by
          rw [← hx]; simp only [mul_assoc]
      _ = _ := by rw [Units.inv_mul, h1, one_mul, mul_one]
  calc ((x' * x⁻¹ : Sˣ) : S) * (σ ((x' * x⁻¹ : Sˣ) : S)).unop
      = x' * (((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop) * (σ x').unop := by
        simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
    _ = algebraMap A S ((t⁻¹ : Aˣ) : A) * ((x' : S) * b * (σ x').unop) := by
        rw [h2]; simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]
    _ = _ := by rw [hx', ← map_mul, mul_comm, Units.val_mul]

theorem triv_quot : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (β : G.C)
    (x x' : (R ⊗[ℚ] G.C)ˣ) (t t' : Rˣ), Triv G R β x t → Triv G R β x' t' →
    ∃ g : UPts G.star R, (g : (R ⊗[ℚ] G.C)ˣ × Rˣ).1 = x' * x⁻¹ := by
  intro p _ G R _ _ β x x' t t' hx hx'
  exact ⟨⟨(x' * x⁻¹, t' * t⁻¹), quot_mul_star (starT G.star R) (inC G R β) x x' t t' hx hx'⟩, rfl⟩

end GlobalTheory.LKMid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormVanishingCombinationChartIndepStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneousForm_vanishing_combination_chart_indep : ∀ (Rg : Type) [CommRing Rg] (A₀ T X : Scheme.{0}) (N : LB A₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (t : T ⟶ Sp Rg) (c : Fin mA → Fin mB → Γ(T, ⊤)) (d : ℕ) (F : MvPolynomial (Fin mB) Rg), F.IsHomogeneous d → ∀ (z : X) (q q' : N.ι), φ z ∈ N.U q → φ z ∈ N.U q' → (MvPolynomial.eval₂Hom (gc (p ≫ t) z) (comb a φ p c z q) F = 0 ↔ MvPolynomial.eval₂Hom (gc (p ≫ t) z) (comb a φ p c z q') F = 0) := by
  first | (exact @GlobalTheory.HomFixUniv.formVanish_chart_indep) | (exact GlobalTheory.HomFixUniv.formVanish_chart_indep) | (intros; apply GlobalTheory.HomFixUniv.formVanish_chart_indep  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentAdeleOfPlacesMulEqSumComponentsStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentAdeleOfPlaces_mul_eq_sum_components : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ∀ a : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * a = ∑ w ∈ S₁, GlobalTheory.CompanionTheory.SaGen.iB (GlobalTheory.CompanionTheory.SaGen.placeMapInf w) (Algebra.TensorProduct.map (GlobalTheory.CompanionTheory.SaGen.placeMapInf w).proj (AlgHom.id F E) a) + ∑ v ∈ S₂, GlobalTheory.CompanionTheory.SaGen.iB (GlobalTheory.CompanionTheory.SaGen.placeMapFin v) (Algebra.TensorProduct.map (GlobalTheory.CompanionTheory.SaGen.placeMapFin v).proj (AlgHom.id F E) a) := by
  first | exact @GlobalTheory.PlaceIdemSum.idem_mul_eq_sum | exact GlobalTheory.PlaceIdemSum.idem_mul_eq_sum | (intros; apply GlobalTheory.PlaceIdemSum.idem_mul_eq_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedSpecialUnitarySupportedAtPlacesStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_specialUnitarySupportedAtPlaces : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (ε : AF F), IsClosed (SUSupp σ J ε) := by
  first | exact @GlobalTheory.SUSuppClosed.isClosed_SUSupp | exact GlobalTheory.SUSuppClosed.isClosed_SUSupp | (intros; apply GlobalTheory.SUSuppClosed.isClosed_SUSupp <;> assumption)
end

