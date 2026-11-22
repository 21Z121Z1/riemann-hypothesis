import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1457
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1449
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1455
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0128
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0022

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay

namespace GlobalTheory.ThKTorus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F) in

def tAd (s : ℝ) : AF F := 1 + realAd F (s - 1)

def blkScale {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ) (s : Fin q → ℝ) (z : κ → AF F) : κ → AF F :=
  fun j => (∏ i, if j ∈ blk i then tAd F (s i) else 1) * z j

def IsFrameCo (σ : E →ₐ[F] E) {n d q : ℕ} (J : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (x y : Fin q → Fin n → E) (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J) (incM F JW)) (Fin n × Fin d))
    (blk : Fin q → Finset (Fin n × Fin d)) : Prop :=
  (∀ i j, i ≠ j → Disjoint (blk i) (blk j)) ∧
  ∀ (t : Fin q → ℝ) (a : UA σ J), (∀ i, 0 < t i) → IsTorusU x y t a → ∀ z : Fin n × Fin d → AF F,
    co.e (mat a * co.e.symm (z, 0)) = (blkScale blk (fun i => (t i)⁻¹) z, 0) ∧
    co.e (mat a * co.e.symm (0, z)) = (0, blkScale blk t z)

def majW {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ) (A N : ℕ) (t : Fin q → ℝ) (ξ : κ → F) : ℝ :=
  (∏ i, t i) ^ A * ((∏ i, (1 + t i * ∑ j ∈ blk i, ∑ w : InfinitePlace F, w (ξ j)) ^ N) *
    (1 + ∑ j, ∑ w : InfinitePlace F, w (ξ j)) ^ N)⁻¹

open Classical in

def majI {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ) (A N m : ℕ) (t : Fin q → ℝ) (ξ : κ → F) : ℝ :=
  if ∀ j, IsIntegral ℤ ((m : F) * ξ j) then majW blk A N t ξ else 0

open Classical in

def latG {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ) (A N m : ℕ) (t : Fin q → ℝ) (ξ : κ → F) : ℝ :=
  if ∀ i, ∃ j ∈ blk i, ξ j ≠ 0 then majI blk A N m t ξ else 0

theorem majW_nonneg {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ) (A N : ℕ) (t : Fin q → ℝ) (ξ : κ → F)
    (ht : ∀ i, 0 ≤ t i) : 0 ≤ majW blk A N t ξ := by
  unfold majW
  refine mul_nonneg (pow_nonneg (Finset.prod_nonneg fun i _ => ht i) _) (inv_nonneg.2 (mul_nonneg ?_ ?_))
  · exact Finset.prod_nonneg fun i _ => pow_nonneg (add_nonneg zero_le_one
      (mul_nonneg (ht i) (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun w _ => (apply_nonneg w _)))) _
  · exact pow_nonneg (add_nonneg zero_le_one (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun w _ => (apply_nonneg w _))) _

theorem majI_nonneg {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ) (A N m : ℕ) (t : Fin q → ℝ) (ξ : κ → F)
    (ht : ∀ i, 0 ≤ t i) : 0 ≤ majI blk A N m t ξ := by
  unfold majI; split_ifs
  · exact majW_nonneg blk A N t ξ ht
  · exact le_rfl

theorem latG_nonneg {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ) (A N m : ℕ) (t : Fin q → ℝ) (ξ : κ → F)
    (ht : ∀ i, 0 ≤ t i) : 0 ≤ latG blk A N m t ξ := by
  unfold latG; split_ifs
  · exact majI_nonneg blk A N m t ξ ht
  · exact le_rfl

end GlobalTheory.ThKTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
section
noncomputable section

namespace GlobalTheory.IwLine

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_eq_sigR (σ : E →ₐ[F] E) (z : AE F E) : cA σ z = sigR (AF F) σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem UG_eq_HR (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    GlobalTheory.WeilM.UG (cA σ) (incM F J) = HR (AF F) σ Jᵀ := by
  have hc : ∀ M : Matrix (Fin n) (Fin n) (AE F E), M.map (cA σ) = M.map (sigR (AF F) σ) := fun M => by
    ext i j; exact cA_eq_sigR σ _
  have hJ : JR (AF F) Jᵀ = (incM F J)ᵀ := rfl
  ext g
  change (g.1)ᵀ * incM F J * (g.1).map (cA σ) = incM F J ↔ cT (sigR (AF F) σ) g.1 * JR (AF F) Jᵀ * g.1 = JR (AF F) Jᵀ
  rw [hc, hJ, cT]
  constructor
  · intro h
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  · intro h
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def ofGAd : GAd σ Jᵀ ≃* UA σ J := MulEquiv.subgroupCongr (UG_eq_HR σ J).symm

theorem mat_ofGAd (g : GAd σ Jᵀ) : mat (ofGAd σ J g) = (matHom (AF F) σ Jᵀ g).1 := rfl

theorem matHom_ofGAd_symm (g : UA σ J) : (matHom (AF F) σ Jᵀ ((ofGAd σ J).symm g)).1 = mat g := rfl

def lineStab (x : Fin n → E) : Subgroup (UA σ J) where
  carrier := {g | ∃ a : (AE F E)ˣ, mat g *ᵥ incV F x = (a : AE F E) • incV F x}
  one_mem' := ⟨1, by simp [mat, Matrix.one_mulVec]⟩
  mul_mem' := by
    rintro g h ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨b * a, ?_⟩
    show (mat g * mat h) *ᵥ incV F x = _
    rw [← Matrix.mulVec_mulVec, hb, Matrix.mulVec_smul, ha, smul_smul, Units.val_mul]
  inv_mem' := by
    rintro g ⟨a, ha⟩
    refine ⟨a⁻¹, ?_⟩
    have e : mat g⁻¹ *ᵥ (mat g *ᵥ incV F x) = incV F x := by
      rw [Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mulVec]
    rw [ha, Matrix.mulVec_smul] at e
    calc mat g⁻¹ *ᵥ incV F x = ((a⁻¹ : (AE F E)ˣ) : AE F E) • ((a : AE F E) • mat g⁻¹ *ᵥ incV F x) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = _ := by rw [e]

theorem mem_lineStab {x : Fin n → E} {g : UA σ J} :
    g ∈ lineStab σ J x ↔ ∃ a : (AE F E)ˣ, mat g *ᵥ incV F x = (a : AE F E) • incV F x := Iff.rfl

end GlobalTheory.IwLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixEntriesBoundedAlmostEverywhere
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.FixedBound

theorem exists_entry_absFin_bound {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (Y : Matrix (Fin n) (Fin d) (AF F ⊗[F] E)) : ∃ K : HeightOneSpectrum (𝓞 F) → ℝ≥0, (Function.mulSupport K).Finite ∧ (∀ v, 1 ≤ K v) ∧ ∀ v, (Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (Y p.1 p.2))) ≤ K v := by
  refine ⟨fun v => max 1 (Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (Y p.1 p.2))),
    ?_, fun v => le_max_left _ _, fun v => le_max_right _ _⟩
  have h := Filter.eventually_all.2 fun p : Fin n × Fin d => GlobalTheory.AdelicU.eventually_absFin_le_one F (Y p.1 p.2)
  refine (Filter.eventually_cofinite.1 h).subset fun v hv hv' => hv ?_
  exact max_eq_left (Finset.sup_le fun p _ => hv' p)

end GlobalTheory.FixedBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOfSkewHermitianTwist
section
noncomputable section

namespace GlobalTheory.ThK.SqIntMaxCpt

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped Matrix TensorProduct

theorem exists_congr_one {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.IsHermitian)
    (hpos : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) : ∃ Q : GL (Fin n) ℂ, Q.1ᴴ * P * Q.1 = 1 := by
  have hd : P.det ≠ 0 := fun h => by
    obtain ⟨x, hx, e⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    simpa [e] using hpos x hx
  obtain ⟨ε, Q, hQ⟩ := Frames.exists_congr_diagonal_sign hP hd
  refine ⟨Q, hQ.trans ?_⟩
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  have hx : Q.1 *ᵥ (Pi.single i 1 : Fin n → ℂ) ≠ 0 := fun h => by
    have := congrArg ((Q⁻¹).1 *ᵥ ·) h
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    simpa using congrFun this i
  have := hpos _ hx
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hQ] at this
  cases h : ε i
  · simp [h, Matrix.mulVec_single_one, dotProduct, Pi.single_apply, Matrix.diagonal_apply] at this
    linarith
  · simp

theorem exists_unitary_sign {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (h2 : H * H = 1) :
    ∃ (ε : Fin n → Bool) (U : GL (Fin n) ℂ), U.1ᴴ * U.1 = 1 ∧
      U.1ᴴ * H * U.1 = Matrix.diagonal fun i => if ε i then 1 else -1 := by
  set U : Matrix (Fin n) (Fin n) ℂ := hH.eigenvectorUnitary.1 with hU
  have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hH.eigenvectorUnitary.2
  have h1' : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hH.eigenvectorUnitary.2
  have h3 : Uᴴ * H * U = Matrix.diagonal fun i => (hH.eigenvalues i : ℂ) := by
    have := hH.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def] using this
  have h4 : (Uᴴ * H * U) * (Uᴴ * H * U) = 1 := by
    calc _ = Uᴴ * (H * (U * Uᴴ) * H) * U := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1', Matrix.mul_one, h2, Matrix.mul_one, h1]
  rw [h3, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one] at h4
  refine ⟨fun i => decide ((hH.eigenvalues i : ℂ) = 1), ⟨U, Uᴴ, h1', h1⟩, h1, h3.trans ?_⟩
  congr 1
  funext i
  have := congrFun (Matrix.diagonal_injective h4) i
  rcases mul_self_eq_one_iff.1 this with h | h
  · simp [h]
  · simp [h]

theorem exists_frame {n : ℕ} {M θ G : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) (hθ : IsCartan M θ) {s : ℝ} (hs : s ≠ 0)
    (hG : G = (s : ℂ) • M.map star) : ∃ (ε : Fin n → Bool) (Q : GL (Fin n) ℂ),
      Q.1ᴴ * G * Q.1 = Matrix.diagonal (fun i => if ε i then 1 else -1) ∧
      ∀ k : Matrix (Fin n) (Fin n) ℂ, kᴴ * G * k = G → ((Q⁻¹).1 * k * Q.1)ᴴ * ((Q⁻¹).1 * k * Q.1) = 1 → Commute k θ := by
  obtain ⟨h1, h2, h3⟩ := hθ
  set N := M.map star with hN
  have hNh : Nᴴ = N := by
    ext i j
    simpa [hN] using congrArg star (congrFun (congrFun hM i) j)
  have h2' : θᴴ * N * θ = N := by
    have := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A.map (starRingEnd ℂ)) h2
    simp only [Matrix.map_mul] at this
    have e1 : θᵀ.map (starRingEnd ℂ) = θᴴ := by ext i j; simp
    have e2 : (θ.map star).map (starRingEnd ℂ) = θ := by ext i j; simp
    rw [e1, e2] at this
    exact this
  have h4 : θᴴ * N = N * θ := by
    conv_rhs => rw [← h2', Matrix.mul_assoc, h1, Matrix.mul_one]
  obtain ⟨e, he, hes⟩ : ∃ e : ℝ, e * e = 1 ∧ 0 < s * e := by
    rcases lt_or_gt_of_ne hs with h | h
    · exact ⟨-1, by norm_num, by linarith⟩
    · exact ⟨1, by norm_num, by linarith⟩
  have he' : (e : ℂ) * e = 1 := by exact_mod_cast he
  set T := (e : ℂ) • θ with hT
  have hTT : T * T = 1 := by rw [hT, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he', one_smul, h1]
  have hGT : G * T = ((s * e : ℝ) : ℂ) • (θᴴ * N) := by
    rw [hG, hT, h4, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.ofReal_mul]
  have hGh : Gᴴ = G := by rw [hG, Matrix.conjTranspose_smul, hNh]; simp
  have hP : (G * T).IsHermitian := by
    rw [Matrix.IsHermitian, hGT, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hNh,
      Matrix.conjTranspose_conjTranspose, ← h4]
    simp
  obtain ⟨Q₀, hQ₀⟩ := exists_congr_one hP fun x hx => by
    have e1 : star x ⬝ᵥ (θᴴ * N) *ᵥ x = star ((θ *ᵥ x) ⬝ᵥ M *ᵥ star x) := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
      simp [dotProduct, Matrix.mulVec, hN, mul_comm]
    rw [hGT, Matrix.smul_mulVec, dotProduct_smul, e1, smul_eq_mul, Complex.re_ofReal_mul]
    exact mul_pos hes (by simpa using h3 x hx)
  have h5 : Q₀.1ᴴ * G = (Q₀⁻¹).1 * T := by
    have := congrArg (· * (Q₀⁻¹).1 * T) hQ₀
    simpa only [Matrix.mul_assoc, Units.mul_inv_cancel_left, hTT, Matrix.mul_one, Matrix.one_mul] using this
  obtain ⟨ε, U, hU, hUH⟩ := exists_unitary_sign (H := Q₀.1ᴴ * G * Q₀.1)
    (Matrix.isHermitian_conjTranspose_mul_mul _ hGh) (by
      rw [h5]
      simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]
      rw [← Matrix.mul_assoc T, hTT, Matrix.one_mul, Units.inv_mul])
  refine ⟨ε, Q₀ * U, by simpa [Matrix.mul_assoc] using hUH, fun k hk hu => ?_⟩
  set Q := Q₀ * U with hQ
  have hQP : Q.1ᴴ * (G * T) * Q.1 = 1 := by
    calc _ = U.1ᴴ * (Q₀.1ᴴ * (G * T) * Q₀.1) * U.1 := by simp [hQ, Matrix.mul_assoc]
      _ = 1 := by rw [hQ₀, Matrix.mul_one, hU]
  have hi : (Q⁻¹).1ᴴ * Q.1ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
  have hPe : G * T = (Q⁻¹).1ᴴ * (Q⁻¹).1 := by
    have := congrArg (fun A => (Q⁻¹).1ᴴ * A * (Q⁻¹).1) hQP
    simpa only [← Matrix.mul_assoc, hi, Matrix.one_mul, Matrix.mul_one, Units.mul_inv_cancel_right] using this
  have hkP : kᴴ * (G * T) * k = G * T := by
    have := congrArg (fun A => (Q⁻¹).1ᴴ * A * (Q⁻¹).1) hu
    rw [hPe]
    simpa only [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, hi, Matrix.one_mul, Matrix.mul_one,
      Units.mul_inv_cancel_right] using this
  have hL : (Q.1 * Q.1ᴴ) * G * T = 1 := by
    rw [Matrix.mul_assoc, hPe, Matrix.mul_assoc, ← Matrix.mul_assoc Q.1ᴴ, ← Matrix.conjTranspose_mul, Units.inv_mul,
      Matrix.conjTranspose_one, Matrix.one_mul, Units.mul_inv]
  have hGu : IsUnit G := by
    have : IsUnit (Q.1 * Q.1ᴴ * G) := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hL)
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at this
    exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right this)
  have hkG : IsUnit (kᴴ * G) := by
    rw [← hk, Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at hGu
    exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left hGu)
  have hc : k * T = T * k := hkG.mul_left_cancel (by
    rw [← Matrix.mul_assoc, hk, ← hkP]; simp only [Matrix.mul_assoc])
  have := congrArg ((e : ℂ) • ·) hc
  simpa only [hT, Matrix.mul_smul, Matrix.smul_mul, smul_smul, he', one_smul, Commute, SemiconjBy] using this

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem at_evI_of_compFin {z : AE F E} (h : ∀ v, compFin F E v z = 0) : At (evI F) z := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  refine GlobalTheory.Doubling.adele_ext (fun w => ?_) fun v => ?_
  · rw [Algebra.smul_def, map_mul, map_zero]
    refine mul_eq_zero_of_left ?_ _
    change evInf F w u ⊗ₜ[F] (1 : E) = 0
    rw [show evInf F w u = 0 from congrFun h1 w, TensorProduct.zero_tmul]
  · rw [Algebra.smul_def, map_mul, h, mul_zero, map_zero]

theorem exists_isMaxCpt_le_kInf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (d r s : ℕ) (W : Spc F E d), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∃ K, IsMaxCpt σ (c • W.J.map σ) K ∧ ∀ k ∈ K, (toGAd hσ W.J hc).symm k ∈ KInf σ W B.emb := by
  intro F E _ _ _ _ _ σ hσ B d r s W hB hW c hc hσc
  have h := hB.cm
  have hcj : ∀ (τ : E →+* ℂ) x, star (τ x) = τ (σ x) := fun τ x => (h.2.2.2 τ x).symm
  have key : ∀ w : InfinitePlace F, ∃ (ε : Fin d → Bool) (Q : GL (Fin d) ℂ),
      Q.1ᴴ * (c • W.J.map σ).map (B.emb w).1 * Q.1 = Matrix.diagonal (fun i => if ε i then 1 else -1) ∧
      ∀ k : Matrix (Fin d) (Fin d) ℂ, kᴴ * (c • W.J.map σ).map (B.emb w).1 * k = (c • W.J.map σ).map (B.emb w).1 →
        ((Q⁻¹).1 * k * Q.1)ᴴ * ((Q⁻¹).1 * k * Q.1) = 1 → Commute k (W.θ w) := fun w => by
    have hre : ((B.emb w).1 c).re = 0 := by
      have := congrArg Complex.re (hcj (B.emb w).1 c)
      rw [hσc, map_neg] at this
      simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at this
      linarith
    have him : ((B.emb w).1 c).im ≠ 0 := fun e =>
      (map_ne_zero (B.emb w).1).2 hc (Complex.ext hre e)
    refine exists_frame (s := -((B.emb w).1 c).im) ?_ (hW.cartan w) (neg_ne_zero.2 him) ?_
    · ext i j
      simp [hcj, hW.skew]
    · ext i j
      have e : (B.emb w).1 c = ((B.emb w).1 c).im * Complex.I := by
        conv_lhs => rw [← Complex.re_add_im ((B.emb w).1 c), hre]
        simp
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, star_mul', hcj]
      conv_lhs => rw [e]
      simp [mul_assoc]
  choose ε Q hQ hk using key
  let e := fun w : InfinitePlace F => RingEquiv.ofBijective _ (infEmb_bijective h (B.emb w))
  let b := fun w : InfinitePlace F => Formalism.UG.bc (e w).symm.toRingHom (Q w)
  have h1 : ∀ w, (b w).1.map (infEmb (B.emb w)) = (Q w).1 := fun w => Matrix.ext fun i j => (e w).apply_symm_apply _
  have h1' : ∀ w, ((b w)⁻¹).1.map (infEmb (B.emb w)) = ((Q w)⁻¹).1 := fun w =>
    Matrix.ext fun i j => (e w).apply_symm_apply _
  have h2 : ∀ w, (JR w.Completion (c • W.J.map σ)).map (infEmb (B.emb w)) = (c • W.J.map σ).map (B.emb w).1 := fun w => by
    ext r s; simp [JR, inclR]
  refine ⟨majCpt σ _ b, isMaxCpt_majCpt h fun w => ⟨ε w, Matrix.map_injective (e w).injective ?_⟩, fun k hkK => ?_⟩
  · change Matrix.map _ (infEmb (B.emb w)) = Matrix.map _ (infEmb (B.emb w))
    rw [Matrix.map_mul, Matrix.map_mul, Frames.map_cT_sigR h, h1, h2, hQ, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    split_ifs <;> simp
  obtain ⟨hk1, hk2⟩ := mem_majCpt.1 hkK
  have hm : mat ((toGAd hσ W.J hc).symm k) = (matHom _ σ _ k).1 := rfl
  refine ⟨fun u hu => Matrix.ext fun i j => at_evI_of_compFin (fun v => ?_) u hu, fun w => ?_⟩
  · have := congrArg (fun g => (matHom _ σ _ g).1 i j) (mem_infPts_iff_forall.1 hk1 v)
    rw [hm, Matrix.sub_apply, map_sub, sub_eq_zero]
    refine this.trans ?_
    simp [Matrix.one_apply, apply_ite (compFin F E v)]
  · have e1 : (mat ((toGAd hσ W.J hc).symm k)).map (piInf (B.emb w)) =
        (matHom _ σ _ (projArch σ _ w k)).1.map (infEmb (B.emb w)) := rfl
    rw [e1]
    refine hk w _ ?_ ?_
    · have : Formalism.UG.cT (sigR _ σ) (matHom _ σ _ (projArch σ _ w k)).1 * JR w.Completion (c • W.J.map σ) *
        (matHom _ σ _ (projArch σ _ w k)).1 = JR w.Completion (c • W.J.map σ) := (projArch σ _ w k).2
      have := congrArg (fun A => A.map (infEmb (B.emb w))) this
      simpa only [Matrix.map_mul, Frames.map_cT_sigR h, h2] using this
    · have : Formalism.UG.cT (sigR _ σ) ((b w)⁻¹ * matHom _ σ _ (projArch σ _ w k) * b w).1 * 1 *
        ((b w)⁻¹ * matHom _ σ _ (projArch σ _ w k) * b w).1 = 1 := mem_stabArch.1 (hk2 w)
      have := congrArg (fun A => A.map (infEmb (B.emb w))) this
      simpa only [Matrix.mul_one, Matrix.map_mul, Frames.map_cT_sigR h, Units.val_mul, h1, h1',
        Matrix.map_one _ (map_zero _) (map_one _)] using this

end GlobalTheory.ThK.SqIntMaxCpt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
section
noncomputable section

namespace GlobalTheory.IndLine

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d d₁ : ℕ} {Y : Spc F E n} {W : Spc F E d}

def IsTwEig (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ) (x : P) : Prop :=
  ∀ k ∈ KInf σ W B.emb, ∀ t : (AE F E)ˣ, IsLevi H' t (1 : UA σ W₁.J) k → ∀ f ∈ M.Pol B.ψ B.emb,
    ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₁ → p f = x →
      p f₁ = ((χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ)) • x

def IsOffEig (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ) (x : P) : Prop :=
  ∃ k ∈ KInf σ W B.emb, ∃ t : (AE F E)ˣ, IsLevi H' t (1 : UA σ W₁.J) k ∧ ∃ c : ℂ,
    c ≠ (χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ) ∧ ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, k)) f f₁ → p f = x → p f₁ = c • x

def twPart (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ)
    (V : Submodule ℂ P) : Submodule ℂ P :=
  Submodule.span ℂ {x | x ∈ V ∧ IsTwEig B M om p W₁ H' χ z x}

def offPart (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ)
    (V : Submodule ℂ P) : Submodule ℂ P :=
  Submodule.span ℂ {x | x ∈ V ∧ IsOffEig B M om p W₁ H' χ z x}

def KStabL (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (N : Submodule ℂ P) : Prop :=
  ∀ k ∈ KInf σ W B.emb, ∀ k₁ ∈ KInf σ W₁ B.emb, IsLevi H' 1 k₁ k → ∀ f ∈ M.Pol B.ψ B.emb,
    ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₁ → p f ∈ N → p f₁ ∈ N

theorem twPart_le (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ)
    (V : Submodule ℂ P) : twPart B M om p W₁ H' χ z V ≤ V :=
  Submodule.span_le.2 fun _ hx => hx.1

end GlobalTheory.IndLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneAddNormPowLeSumLinearFormPow
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

namespace GlobalTheory.ArchDecay

theorem onePlusNormPow_le_sum_linearForm_pow : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : ℕ), ∃ (K : ℕ) (l : Fin K → (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (C : ℝ), (∀ j, ‖l j‖ ≤ 1) ∧ ∀ y, (1 + ‖y‖) ^ N ≤ C * (1 + ∑ j, |l j y| ^ N) := by
  intro F _ _ κ _ N
  let b := Module.finBasis ℝ (κ → mixedEmbedding.mixedSpace F)
  let K := Module.finrank ℝ (κ → mixedEmbedding.mixedSpace F)
  let c : Fin K → (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
    fun j => LinearMap.toContinuousLinearMap (b.coord j)
  let w : Fin K → ℝ := fun j => (1 + ‖c j‖) * ‖b j‖
  have hw : ∀ j, 0 ≤ w j := fun j => by positivity
  let W : ℝ := 1 + ∑ j, w j
  have hW1 : 1 ≤ W := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hw j); simp only [W]; linarith
  have hwW : ∀ j, w j ≤ W := fun j => by
    have := Finset.single_le_sum (f := w) (fun j _ => hw j) (Finset.mem_univ j)
    simp only [W]; linarith
  let l : Fin K → (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ := fun j => (1 + ‖c j‖)⁻¹ • c j
  have hl : ∀ j, ‖l j‖ ≤ 1 := fun j => by
    have h0 : 0 < 1 + ‖c j‖ := by positivity
    simp only [l, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos h0]
    rw [inv_mul_le_iff₀ h0]; linarith
  have hlw : ∀ j y, |l j y| * w j = |b.repr y j| * ‖b j‖ := fun j y => by
    have h0 : 0 < 1 + ‖c j‖ := by positivity
    simp only [l, w, c, ContinuousLinearMap.smul_apply, LinearMap.coe_toContinuousLinearMap',
      Module.Basis.coord_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos h0]
    field_simp
  have hnorm : ∀ y, ‖y‖ ≤ ∑ j, |l j y| * w j := fun y => by
    calc ‖y‖ = ‖∑ j, b.repr y j • b j‖ := by rw [b.sum_repr y]
      _ ≤ ∑ j, ‖b.repr y j • b j‖ := norm_sum_le _ _
      _ = ∑ j, |l j y| * w j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hlw, norm_smul, Real.norm_eq_abs]
  refine ⟨K, l, ((K : ℝ) + 1) ^ N * W ^ N, hl, fun y => ?_⟩
  have hS : 0 ≤ ∑ j, |l j y| ^ N := Finset.sum_nonneg fun j _ => by positivity
  rcases N with _ | n
  · simp only [pow_zero, one_mul]
    have : (0:ℝ) ≤ ∑ _x : Fin K, (1:ℝ) := by positivity
    linarith
  let f : Option (Fin K) → ℝ := fun o => Option.elim o 1 fun j => |l j y| * w j
  have hf : ∀ o ∈ (Finset.univ : Finset (Option (Fin K))), 0 ≤ f o := by
    intro o _; cases o with
    | none => simp [f]
    | some j => simp only [f, Option.elim_some]; exact mul_nonneg (abs_nonneg _) (hw j)
  have h1 : 1 + ‖y‖ ≤ ∑ o, f o := by
    rw [Fintype.sum_option]; simp only [f, Option.elim_none, Option.elim_some]
    linarith [hnorm y]
  have h2 := pow_sum_le_card_mul_sum_pow hf n
  rw [Finset.card_univ, Fintype.card_option, Fintype.card_fin, Fintype.sum_option] at h2
  simp only [f, Option.elim_none, Option.elim_some, one_pow] at h2
  have h3 : ∑ j, (|l j y| * w j) ^ (n + 1) ≤ W ^ (n + 1) * ∑ j, |l j y| ^ (n + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hw j) (hwW j) _) (by positivity)
  have hW : 1 ≤ W ^ (n + 1) := one_le_pow₀ hW1
  have hK : ((K : ℝ) + 1) ^ n ≤ ((K : ℝ) + 1) ^ (n + 1) :=
    pow_le_pow_right₀ (by linarith [(K.cast_nonneg : (0:ℝ) ≤ K)]) (Nat.le_succ n)
  have hKn : 0 ≤ ((K : ℝ) + 1) ^ n := by positivity
  calc (1 + ‖y‖) ^ (n + 1) ≤ (∑ o, f o) ^ (n + 1) :=
        pow_le_pow_left₀ (by positivity) h1 _
    _ ≤ ((K : ℝ) + 1) ^ n * (1 + ∑ j, (|l j y| * w j) ^ (n + 1)) := by
        rw [Fintype.sum_option]; simpa [f] using h2
    _ ≤ ((K : ℝ) + 1) ^ n * (W ^ (n + 1) * (1 + ∑ j, |l j y| ^ (n + 1))) := by
        gcongr; nlinarith
    _ ≤ ((K : ℝ) + 1) ^ (n + 1) * W ^ (n + 1) * (1 + ∑ j, |l j y| ^ (n + 1)) := by
        rw [← mul_assoc]; gcongr

end GlobalTheory.ArchDecay
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPlaceComponentAdeleConjugationEqComplexConjStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaceComponent_adeleConjugation_eq_complexConj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (z : AE F E), piInf τ (cA σ z) = star (piInf τ z) := by
  first | exact @GlobalTheory.RealPlaceConj.piInf_cA_eq_star | exact GlobalTheory.RealPlaceConj.piInf_cA_eq_star | (intros; apply GlobalTheory.RealPlaceConj.piInf_cA_eq_star <;> assumption)
end

