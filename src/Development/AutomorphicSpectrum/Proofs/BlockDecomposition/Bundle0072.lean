import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0048
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.OneSTr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0038
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FibreFactorHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0049
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0050

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationAddStatement
section
open CrystallineSemistableComparison.Pb.Kap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realization_add : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) {j : ℕ} (x y : ∀ n, C.S n j) (f g : Module.Dual K (C.V j) →+ B), C.Rho x f → C.Rho y g → C.Rho (x + y) (f + g) := by
  first | exact @GlobalTheory.CompanionTheory.KapRho.rho_add | exact GlobalTheory.CompanionTheory.KapRho.rho_add | (intros; apply GlobalTheory.CompanionTheory.KapRho.rho_add <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationCupProductStatement
section
open CrystallineSemistableComparison.Pb.Kap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realization_cup_product : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) (hC : C.Good) (P : Cup C), P.Good → ∀ {i j : ℕ} (x : ∀ n, C.S n i) (y : ∀ n, C.S n j) (f : Module.Dual K (C.V i) →+ B) (g : Module.Dual K (C.V j) →+ B) (h : Module.Dual K (C.V (i + j)) →+ B), C.Rho x f → C.Rho y g → C.Rho (fun n => P.cS n i j (x n) (y n)) h → ∀ {m m' : ℕ} (bs : Module.Basis (Fin m) K (C.V i)) (bs' : Module.Basis (Fin m') K (C.V j)) (φ : Module.Dual K (C.V (i + j))), h φ = ∑ s, ∑ s', f (bs.coord s) * g (bs'.coord s') * C.o (φ (P.cV i j (bs s) (bs' s'))) := by
  first | exact @GlobalTheory.CompanionTheory.KapRho.rho_cup | exact GlobalTheory.CompanionTheory.KapRho.rho_cup | (intros; apply GlobalTheory.CompanionTheory.KapRho.rho_cup <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationFunctorialStatement
section
open CrystallineSemistableComparison.Pb.Kap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realization_functorial : ∀ {Λ A B K Λ' A' B' : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] [CommRing Λ'] [CommRing A'] [CommRing B'] (C : Chain.{1} Λ A B K) (C' : Chain.{1} Λ' A' B' K) (h : Hom C C'), C.Good → C'.Good → h.Good → ∀ {j : ℕ} (x : ∀ n, C.S n j) (f : Module.Dual K (C.V j) →+ B), C.Rho x f → C'.Rho (fun n => h.fS n j (x n)) (h.tr j f) := by
  first | exact @GlobalTheory.CompanionTheory.KapRhoHom.rho_hom | exact GlobalTheory.CompanionTheory.KapRhoHom.rho_hom | (intros; apply GlobalTheory.CompanionTheory.KapRhoHom.rho_hom <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationSmulStatement
section
open CrystallineSemistableComparison.Pb.Kap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realization_smul : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) {j : ℕ} (c : Λ) (x : ∀ n, C.S n j) (f : Module.Dual K (C.V j) →+ B), C.Rho x f → C.Rho (c • x) ((AddMonoidHom.mulLeft (C.ι (C.lam c))).comp f) := by
  first | exact @GlobalTheory.CompanionTheory.KapChain.rho_smul | exact GlobalTheory.CompanionTheory.KapChain.rho_smul | (intros; apply GlobalTheory.CompanionTheory.KapChain.rho_smul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationUniqueStatement
section
open CrystallineSemistableComparison.Pb.Kap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realization_unique : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) (hC : C.Good) {j : ℕ} (x : ∀ n, C.S n j) (f f' : Module.Dual K (C.V j) →+ B), C.Rho x f → C.Rho x f' → f = f' := by
  first | exact @GlobalTheory.CompanionTheory.KapUniq.rho_unique | exact GlobalTheory.CompanionTheory.KapUniq.rho_unique | (intros; apply GlobalTheory.CompanionTheory.KapUniq.rho_unique <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationUnitClassStatement
section
open CrystallineSemistableComparison.Pb.Kap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realization_unit_class : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) (hC : C.Good) (P : Cup C), P.Good → ∀ h : Module.Dual K (C.V 0) →+ B, C.Rho P.oneS h → ∀ φ : Module.Dual K (C.V 0), h φ = C.o (φ P.oneV) := by
  first | exact @GlobalTheory.CompanionTheory.KapUnit.rho_one_eval | exact GlobalTheory.CompanionTheory.KapUnit.rho_one_eval | (intros; apply GlobalTheory.CompanionTheory.KapUnit.rho_one_eval <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionCorankEqRankLowerLeft
section
open Matrix GlobalTheory.CompanionTheory.Jp

noncomputable section

namespace GlobalTheory.CompanionTheory.Jp.RedRank

theorem rank_add_rank_eq {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {n : ℕ} {ϖ : O}
    (hϖ : Irreducible ϖ) (d E : Matrix (Fin n) (Fin n) O) (hdE : d * E = ϖ • (1 : Matrix (Fin n) (Fin n) O))
    (hEd : E * d = ϖ • (1 : Matrix (Fin n) (Fin n) O)) :
    (d.map (IsLocalRing.residue O)).rank + (E.map (IsLocalRing.residue O)).rank = n := by
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ |>.1 hϖ
  have hres : IsLocalRing.residue O ϖ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, hmax]
    exact Ideal.mem_span_singleton_self ϖ
  have hzero : d.map (IsLocalRing.residue O) * E.map (IsLocalRing.residue O) = 0 := by
    rw [← Matrix.map_mul, hdE]
    ext i j
    simp [hres]
  have hker : LinearMap.ker (d.map (IsLocalRing.residue O)).mulVecLin =
      LinearMap.range (E.map (IsLocalRing.residue O)).mulVecLin := by
    ext x
    constructor
    · intro hx
      have hx' : (d.map (IsLocalRing.residue O)) *ᵥ x = 0 := by simpa using hx
      choose x₀ hx₀ using fun i => IsLocalRing.residue_surjective (x i)
      have hxc : (IsLocalRing.residue O) ∘ x₀ = x := funext hx₀
      have hmem : ∀ i, ∃ y : O, y * ϖ = (d *ᵥ x₀) i := by
        intro i
        have h0 : IsLocalRing.residue O ((d *ᵥ x₀) i) = 0 := by
          rw [RingHom.map_mulVec, hxc, hx']
          rfl
        rw [IsLocalRing.residue_eq_zero_iff, hmax] at h0
        exact Ideal.mem_span_singleton'.1 h0
      choose y hy using hmem
      have hdx : d *ᵥ x₀ = ϖ • y := by
        ext i
        simp [← hy i, mul_comm]
      have hEx : ϖ • x₀ = ϖ • (E *ᵥ y) := by
        have h1 : E *ᵥ (d *ᵥ x₀) = ϖ • x₀ := by
          rw [Matrix.mulVec_mulVec, hEd, Matrix.smul_mulVec, Matrix.one_mulVec]
        rw [← h1, hdx, Matrix.mulVec_smul]
      have hxE : x₀ = E *ᵥ y := smul_right_injective _ hϖ.ne_zero hEx
      refine ⟨(IsLocalRing.residue O) ∘ y, ?_⟩
      ext i
      simp only [Matrix.mulVecLin_apply]
      rw [← RingHom.map_mulVec, ← hxE]
      exact hx₀ i
    · rintro ⟨y, rfl⟩
      simp [Matrix.mulVec_mulVec, hzero]
  have hrn := LinearMap.finrank_range_add_finrank_ker (d.map (IsLocalRing.residue O)).mulVecLin
  rw [hker] at hrn
  simpa [Matrix.rank] using hrn

theorem low_rows {R : Type} [CommRing R] {n : ℕ} (g : GL (Ix n) R) :
    lowerLeftBlock g * (g⁻¹).1.toBlocks₁₂ + dBlk g * (g⁻¹).1.toBlocks₂₂ = 1 := by
  have h : g.1 * (g⁻¹).1 = 1 := by rw [← Units.val_mul]; simp
  have e : fromBlocks g.1.toBlocks₁₁ g.1.toBlocks₁₂ g.1.toBlocks₂₁ g.1.toBlocks₂₂ *
      fromBlocks (g⁻¹).1.toBlocks₁₁ (g⁻¹).1.toBlocks₁₂ (g⁻¹).1.toBlocks₂₁ (g⁻¹).1.toBlocks₂₂ = 1 := by
    rw [fromBlocks_toBlocks, fromBlocks_toBlocks]; exact h
  rw [fromBlocks_multiply, ← fromBlocks_one] at e
  exact (Matrix.fromBlocks_inj.1 e).2.2.2

theorem scM_val {L : Type} [Field L] {n : ℕ} (w : Lˣ) : (scM (n := n) w).1 = (w : L) • (1 : Matrix (Fin n) (Fin n) L) := by
  ext i j
  simp [scM, Matrix.one_apply, Matrix.diagonal_apply]

theorem low_eq {L : Type} [Field L] {n : ℕ} (x : L) (X Y : Matrix (Ix n) (Ix n) L) (a b d : Matrix (Fin n) (Fin n) L)
    (h : X * fromBlocks 1 0 0 (x • (1 : Matrix (Fin n) (Fin n) L)) = fromBlocks a b 0 d * Y) :
    X.toBlocks₂₁ = d * Y.toBlocks₂₁ ∧ x • X.toBlocks₂₂ = d * Y.toBlocks₂₂ := by
  have e : fromBlocks X.toBlocks₁₁ X.toBlocks₁₂ X.toBlocks₂₁ X.toBlocks₂₂ *
        fromBlocks 1 0 0 (x • (1 : Matrix (Fin n) (Fin n) L)) =
      fromBlocks a b 0 d * fromBlocks Y.toBlocks₁₁ Y.toBlocks₁₂ Y.toBlocks₂₁ Y.toBlocks₂₂ := by
    rw [fromBlocks_toBlocks, fromBlocks_toBlocks]; exact h
  rw [fromBlocks_multiply, fromBlocks_multiply] at e
  obtain ⟨-, -, h3, h4⟩ := Matrix.fromBlocks_inj.1 e
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add, Matrix.zero_mul, Matrix.mul_smul] at h3 h4
  exact ⟨h3, h4⟩

theorem exists_integral {O L : Type} [CommRing O] [Field L] (ι : O →+* L) (hι : Function.Injective ι) {n : ℕ} (ϖ : O)
    (C D C' D' Bi Di Bi' Di' : Matrix (Fin n) (Fin n) O) (h1 : C * Bi + D * Di = 1) (h2 : C' * Bi' + D' * Di' = 1)
    (dL dLi : Matrix (Fin n) (Fin n) L) (hd : dL * dLi = 1) (hd' : dLi * dL = 1)
    (hC : C.map ι = dL * C'.map ι) (hD : ι ϖ • D.map ι = dL * D'.map ι) :
    (C * Bi' + ϖ • (D * Di')) * (ϖ • (C' * Bi) + D' * Di) = ϖ • (1 : Matrix (Fin n) (Fin n) O) ∧
    (ϖ • (C' * Bi) + D' * Di) * (C * Bi' + ϖ • (D * Di')) = ϖ • (1 : Matrix (Fin n) (Fin n) O) ∧
    C = (C * Bi' + ϖ • (D * Di')) * C' ∧ (ϖ • (C' * Bi) + D' * Di) * D = D' := by
  have hinj : Function.Injective (ι.mapMatrix (m := Fin n)) := fun A B h => by
    ext i j
    exact hι (congrFun (congrFun h i) j)
  have hs : ∀ M : Matrix (Fin n) (Fin n) O, ι.mapMatrix (ϖ • M) = ι ϖ • ι.mapMatrix M := by
    intro M; ext i j; simp
  have hC' : ι.mapMatrix C = dL * ι.mapMatrix C' := hC
  have hD' : ι ϖ • ι.mapMatrix D = dL * ι.mapMatrix D' := hD
  have h1' : ι.mapMatrix C * ι.mapMatrix Bi + ι.mapMatrix D * ι.mapMatrix Di = 1 := by
    rw [← map_mul, ← map_mul, ← map_add, h1, map_one]
  have h2' : ι.mapMatrix C' * ι.mapMatrix Bi' + ι.mapMatrix D' * ι.mapMatrix Di' = 1 := by
    rw [← map_mul, ← map_mul, ← map_add, h2, map_one]
  have hCi : ι.mapMatrix C' = dLi * ι.mapMatrix C := by
    rw [hC', ← Matrix.mul_assoc, hd', Matrix.one_mul]
  have hDi : ι.mapMatrix D' = ι ϖ • (dLi * ι.mapMatrix D) := by
    rw [← Matrix.mul_smul, hD', ← Matrix.mul_assoc, hd', Matrix.one_mul]
  have hF : ι.mapMatrix (C * Bi' + ϖ • (D * Di')) = dL := by
    rw [map_add, hs, map_mul, map_mul, hC', ← Matrix.smul_mul, hD', Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add,
      h2', Matrix.mul_one]
  have hG : ι.mapMatrix (ϖ • (C' * Bi) + D' * Di) = ι ϖ • dLi := by
    rw [map_add, hs, map_mul, map_mul, hCi, hDi, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← smul_add,
      ← Matrix.mul_add, h1', Matrix.mul_one]
  refine ⟨hinj ?_, hinj ?_, hinj ?_, hinj ?_⟩
  · rw [map_mul, hF, hG, hs, map_one, Matrix.mul_smul, hd]
  · rw [map_mul, hF, hG, hs, map_one, Matrix.smul_mul, hd']
  · rw [map_mul, hF, hC']
  · rw [map_mul, hG, Matrix.smul_mul, hDi]

theorem iD_eq_rank : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
    ∀ (κ : GL (Ix n) O) (h : GL (Ix n) (IsLocalRing.ResidueField O)), IsRed (O := O) w κ h →
      iD h = (lowerLeftBlock (resK κ)).rank := by
  intro O L _ _ _ _ _ _ n ϖ hϖ w hw κ h hred
  obtain ⟨a, d, b, κ', hEq, rfl⟩ := hred
  have hv := congrArg Units.val hEq
  have hlow := low_eq (w : L) (κ.1.map (algebraMap O L)) (κ'.1.map (algebraMap O L)) a.1 b d.1 (by
    have : (tauM (n := n) w).1 = fromBlocks 1 0 0 ((w : L) • (1 : Matrix (Fin n) (Fin n) L)) := by
      simp [tauM, pM, scM_val]
    rw [← this]
    exact hv)
  have hres : IsLocalRing.residue O ϖ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ |>.1 hϖ]
    exact Ideal.mem_span_singleton_self ϖ
  obtain ⟨e1, e2, e3, e4⟩ := exists_integral (algebraMap O L) (IsFractionRing.injective O L) ϖ
    (lowerLeftBlock κ) (dBlk κ) (lowerLeftBlock κ') (dBlk κ') (κ⁻¹).1.toBlocks₁₂ (κ⁻¹).1.toBlocks₂₂ (κ'⁻¹).1.toBlocks₁₂ (κ'⁻¹).1.toBlocks₂₂
    (low_rows κ) (low_rows κ') d.1 (d⁻¹).1 (by rw [← Units.val_mul]; simp) (by rw [← Units.val_mul]; simp)
    hlow.1 (by rw [← hw]; exact hlow.2)
  have hn := rank_add_rank_eq hϖ _ _ e1 e2
  set R := (IsLocalRing.residue O).mapMatrix (m := Fin n) with hR
  have hsz : ∀ M : Matrix (Fin n) (Fin n) O, R (ϖ • M) = 0 := by
    intro M; ext i j; simp [hR, hres]
  have hd0 : (lowerLeftBlock κ * (κ'⁻¹).1.toBlocks₁₂ + ϖ • (dBlk κ * (κ'⁻¹).1.toBlocks₂₂)).map (IsLocalRing.residue O) =
      R (lowerLeftBlock κ) * R (κ'⁻¹).1.toBlocks₁₂ := by
    change R _ = _
    rw [map_add, hsz, add_zero, map_mul]
  have hE0 : (ϖ • (lowerLeftBlock κ' * (κ⁻¹).1.toBlocks₁₂) + dBlk κ' * (κ⁻¹).1.toBlocks₂₂).map (IsLocalRing.residue O) =
      R (dBlk κ') * R (κ⁻¹).1.toBlocks₂₂ := by
    change R _ = _
    rw [map_add, hsz, zero_add, map_mul]
  have r1 : ((lowerLeftBlock κ * (κ'⁻¹).1.toBlocks₁₂ + ϖ • (dBlk κ * (κ'⁻¹).1.toBlocks₂₂)).map (IsLocalRing.residue O)).rank
      = (R (lowerLeftBlock κ)).rank := by
    apply le_antisymm
    · rw [hd0]; exact Matrix.rank_mul_le_left _ _
    · have : R (lowerLeftBlock κ) = (lowerLeftBlock κ * (κ'⁻¹).1.toBlocks₁₂ + ϖ • (dBlk κ * (κ'⁻¹).1.toBlocks₂₂)).map (IsLocalRing.residue O) *
          R (lowerLeftBlock κ') := by
        conv_lhs => rw [e3]
        rw [map_mul]; rfl
      rw [this]; exact Matrix.rank_mul_le_left _ _
  have r2 : ((ϖ • (lowerLeftBlock κ' * (κ⁻¹).1.toBlocks₁₂) + dBlk κ' * (κ⁻¹).1.toBlocks₂₂).map (IsLocalRing.residue O)).rank
      = (R (dBlk κ')).rank := by
    apply le_antisymm
    · rw [hE0]; exact Matrix.rank_mul_le_left _ _
    · have : R (dBlk κ') = (ϖ • (lowerLeftBlock κ' * (κ⁻¹).1.toBlocks₁₂) + dBlk κ' * (κ⁻¹).1.toBlocks₂₂).map (IsLocalRing.residue O) *
          R (dBlk κ) := by
        conv_lhs => rw [← e4]
        rw [map_mul]; rfl
      rw [this]; exact Matrix.rank_mul_le_left _ _
  rw [r1, r2] at hn
  have hc : lowerLeftBlock (resK κ) = R (lowerLeftBlock κ) := rfl
  have hdd : dBlk (resK κ') = R (dBlk κ') := rfl
  unfold iD
  rw [hc, hdd]
  omega

end GlobalTheory.CompanionTheory.Jp.RedRank

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionUniqueUpToParabolic
section
open Matrix GlobalTheory.CompanionTheory.Jp

noncomputable section

namespace GlobalTheory.CompanionTheory.Jp.RedUnique

theorem exists_pM_of_low_zero {k : Type} [Field k] {n : ℕ} (g : GL (Ix n) k)
    (hg : g.1.toBlocks₂₁ = 0) :
    ∃ (a d : GL (Fin n) k) (b : Matrix (Fin n) (Fin n) k), g = pM a d b := by
  have hgb : g.1 = fromBlocks g.1.toBlocks₁₁ g.1.toBlocks₁₂ 0 g.1.toBlocks₂₂ := by
    rw [← hg, fromBlocks_toBlocks]
  have hdet : g.1.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  rw [hgb, det_fromBlocks_zero₂₁] at hdet
  refine ⟨GeneralLinearGroup.mkOfDetNeZero _ (left_ne_zero_of_mul hdet),
    GeneralLinearGroup.mkOfDetNeZero _ (right_ne_zero_of_mul hdet), g.1.toBlocks₁₂, ?_⟩
  apply Units.ext
  exact hgb

theorem low_inv_mul_pM {R : Type} [CommRing R] {n : ℕ} (a₁ d₁ a₂ d₂ : GL (Fin n) R)
    (b₁ b₂ : Matrix (Fin n) (Fin n) R) :
    (((pM a₂ d₂ b₂)⁻¹ * pM a₁ d₁ b₁ : GL (Ix n) R)).1.toBlocks₂₁ = 0 := by
  have h1 : ((pM a₁ d₁ b₁ : GL (Ix n) R)).1 = fromBlocks a₁.1 b₁ 0 d₁.1 := rfl
  have h2 : (((pM a₂ d₂ b₂)⁻¹ : GL (Ix n) R)).1 =
      fromBlocks (a₂⁻¹).1 (-((a₂⁻¹).1 * b₂ * (d₂⁻¹).1)) 0 (d₂⁻¹).1 := rfl
  rw [Units.val_mul, h1, h2, fromBlocks_multiply]
  simp [toBlocks_fromBlocks₂₁]

theorem red_unique : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (w : Lˣ) (κ : GL (Ix n) O) (h₁ h₂ : GL (Ix n) (IsLocalRing.ResidueField O)),
    IsRed (O := O) w κ h₁ → IsRed (O := O) w κ h₂ →
      ∃ (a d : GL (Fin n) (IsLocalRing.ResidueField O)) (b : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O)),
        h₂ = pM a d b * h₁ := by
  intro O L _ _ _ _ _ _ n w κ h₁ h₂ r₁ r₂
  obtain ⟨a₁, d₁, b₁, κ₁, e₁, rfl⟩ := r₁
  obtain ⟨a₂, d₂, b₂, κ₂, e₂, rfl⟩ := r₂
  obtain ⟨c, hcd⟩ : ∃ c : GL (Ix n) O, c = κ₂ * κ₁⁻¹ := ⟨_, rfl⟩
  have hc : inL (L := L) c = (pM a₂ d₂ b₂)⁻¹ * pM a₁ d₁ b₁ := by
    have e : pM a₁ d₁ b₁ * inL (L := L) κ₁ = pM a₂ d₂ b₂ * inL (L := L) κ₂ := e₁.symm.trans e₂
    rw [hcd, map_mul, map_inv, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← e, mul_inv_cancel_right]
  have hlow : (inL (L := L) c).1.toBlocks₂₁ = 0 := by
    rw [hc]; exact low_inv_mul_pM _ _ _ _ _ _
  have hO : ∀ i j, c.1 (Sum.inr i) (Sum.inl j) = 0 := by
    intro i j
    have h0 : algebraMap O L (c.1 (Sum.inr i) (Sum.inl j)) = 0 := congrFun (congrFun hlow i) j
    exact IsFractionRing.injective O L (h0.trans (map_zero _).symm)
  have hk : (resK c).1.toBlocks₂₁ = 0 := by
    ext i j
    change IsLocalRing.residue O (c.1 (Sum.inr i) (Sum.inl j)) = 0
    rw [hO, map_zero]
  obtain ⟨a, d, b, hp⟩ := exists_pM_of_low_zero _ hk
  refine ⟨a, d, b, ?_⟩
  rw [← hp, ← map_mul, hcd, inv_mul_cancel_right]

end GlobalTheory.CompanionTheory.Jp.RedUnique

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularizedExponentialSumStatement
section
open scoped Classical
namespace PositivityTheory.Rg.BcB.F
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularized_exponential_sum : PositivityTheory.Rg.BcB.F.ExpSum := by
  first | exact @GlobalTheory.CompanionTheory.ExpSums.expSum_holds | exact GlobalTheory.CompanionTheory.ExpSums.expSum_holds | (intros; apply GlobalTheory.CompanionTheory.ExpSums.expSum_holds <;> assumption)
end PositivityTheory.Rg.BcB.F
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueAlgebraUnramified
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens

theorem resAlg_of_isUnrQuad : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ),
    ∀ h : IsUnrQuad R σ ϖ q ε, ResAlg (R ⧸ lev ϖ 1) (barσ σ ϖ h.fix_ϖ 1) q ε := by
  intro R _ σ ϖ q ε h
  have hτ : ∀ a : R, barσ σ ϖ h.fix_ϖ 1 (Ideal.Quotient.mk (lev ϖ 1) a) =
      Ideal.Quotient.mk (lev ϖ 1) (σ a) := fun a => Ideal.Quotient.lift_mk _ _ _
  obtain ⟨u, hu, hdec⟩ := h.basis
  refine ⟨?_, ?_, ?_, h.one_lt, h.card, h.eps⟩
  · intro e
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective e
    rw [hτ a, hτ (σ a), h.inv]
  · intro e he hne
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective e
    obtain ⟨x, y, hx, hy, rfl⟩ := hdec a
    rw [hτ] at he
    have hy0 : Ideal.Quotient.mk (lev ϖ 1) y = 0 := by
      have h1 : Ideal.Quotient.mk (lev ϖ 1) (y * (u - σ u)) = 0 := by
        have hxy : y * (u - σ u) = (x + y * u) - σ (x + y * u) := by
          rw [map_add, map_mul, hx, hy]
          ring
        rw [hxy, map_sub, he, sub_self]
      rw [map_mul] at h1
      exact (IsUnit.mul_left_eq_zero (hu.map (Ideal.Quotient.mk (lev ϖ 1)))).mp h1
    have hxe : Ideal.Quotient.mk (lev ϖ 1) (x + y * u) = Ideal.Quotient.mk (lev ϖ 1) x := by
      rw [map_add, map_mul, hy0, zero_mul, add_zero]
    rw [hxe] at hne ⊢
    exact (h.fixLocal x hx fun hmem => hne (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)).map _
  · refine ⟨Ideal.Quotient.mk (lev ϖ 1) u, ?_, ?_⟩
    · have hm := hu.map (Ideal.Quotient.mk (lev ϖ 1))
      rwa [map_sub, ← hτ] at hm
    · intro e
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective e
      obtain ⟨x, y, hx, hy, rfl⟩ := hdec a
      refine ⟨Ideal.Quotient.mk (lev ϖ 1) x, Ideal.Quotient.mk (lev ϖ 1) y, ?_, ?_, ?_⟩
      · rw [hτ, hx]
      · rw [hτ, hy]
      · rw [map_add, map_mul]

end GlobalTheory.CompanionTheory.UnrDens
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueUpperUnipotentLift
section
open Matrix GlobalTheory.CompanionTheory.Jp

namespace GlobalTheory.CompanionTheory.Jp

theorem tauM_val_blocks {L : Type} [Field L] {n : ℕ} (w : Lˣ) :
    ((tauM (n := n) w : GL (Ix n) L) : Matrix (Ix n) (Ix n) L) =
      fromBlocks 1 0 0 ((w : L) • (1 : Matrix (Fin n) (Fin n) L)) := by
  ext i k
  rcases i with i | i <;> rcases k with k | k <;>
    simp [tauM, pM, scM, Matrix.one_apply, Matrix.diagonal_apply]

theorem twist_low : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
    ∀ x : GL (Ix n) (IsLocalRing.ResidueField O), x.1.toBlocks₁₂ = 0 →
      ∃ j j' : GL (Ix n) O, inL j * tauM w = tauM w * inL j' ∧ resK j' = x := by
  intro O L _ _ _ _ _ _ n ϖ hϖ w hw x hx
  classical
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : IsLocalRing.ResidueField O → O, ∀ a, IsLocalRing.residue O (ℓ a) = a :=
    ⟨Function.surjInv IsLocalRing.residue_surjective, Function.surjInv_eq _⟩
  have hmapℓ : ∀ B : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O),
      (B.map ℓ).map (IsLocalRing.residue O) = B := by
    intro B
    ext i k
    simp [hℓ]
  obtain ⟨A, hA⟩ : ∃ A, A = x.1.toBlocks₁₁.map ℓ := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = x.1.toBlocks₂₁.map ℓ := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = x.1.toBlocks₂₂.map ℓ := ⟨_, rfl⟩
  have hred : (fromBlocks A 0 C D).map (IsLocalRing.residue O) = x.1 := by
    rw [Matrix.fromBlocks_map, hA, hC, hD, hmapℓ, hmapℓ, hmapℓ,
      Matrix.map_zero _ (map_zero _), ← hx, Matrix.fromBlocks_toBlocks]
  have hdet : IsUnit (A.det * D.det) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    have h1 : IsLocalRing.residue O (A.det * D.det) = x.1.det := by
      rw [← Matrix.det_fromBlocks_zero₁₂ A C D, RingHom.map_det, RingHom.mapMatrix_apply, hred]
    rw [h1]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp x.isUnit).ne_zero
  let j' : GL (Ix n) O := Matrix.nonsingInvUnit (fromBlocks A 0 C D)
    (by rw [Matrix.det_fromBlocks_zero₁₂]; exact hdet)
  let j : GL (Ix n) O := Matrix.nonsingInvUnit (fromBlocks A 0 (ϖ • C) D)
    (by rw [Matrix.det_fromBlocks_zero₁₂]; exact hdet)
  refine ⟨j, j', ?_, ?_⟩
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, tauM_val_blocks]
    show (fromBlocks A 0 (ϖ • C) D).map (algebraMap O L) * _ =
      _ * (fromBlocks A 0 C D).map (algebraMap O L)
    rw [Matrix.fromBlocks_map, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    congr 1
    · simp
    · simp
    · ext i k
      simp [hw, Matrix.map_apply, Matrix.smul_apply]
      rw [Algebra.smul_def]
    · ext i k
      simp [hw]
  · apply Units.ext
    exact hred

end GlobalTheory.CompanionTheory.Jp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFourierTransformMatrixStatement
section
open scoped Matrix SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_fourier_transform_matrix : ∀ (m n : ℕ) (C s : ℂ), s ≠ 0 → ∀ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∃ ψ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ⇑ψ = fun u => C * ∫ v : Fin m → Fin n → ℂ, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * φ v := by
  first | exact @GlobalTheory.CompanionTheory.FourierMatrix.exists_schwartz_trace_transform | exact GlobalTheory.CompanionTheory.FourierMatrix.exists_schwartz_trace_transform | (intros; apply GlobalTheory.CompanionTheory.FourierMatrix.exists_schwartz_trace_transform <;> assumption)
end

