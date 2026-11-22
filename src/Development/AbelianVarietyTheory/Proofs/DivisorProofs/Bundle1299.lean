import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0134
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0335
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1283
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1265
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1261
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1237

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedConjDeltaOfUnitModNorms
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLat.ClSurj

section Theta

variable {R : Type} [CommRing R] {n : ℕ}

theorem Phi_transpose' : (GlobalTheory.Tw.Phi n R)ᵀ = (-1 : R) ^ (n + 1) • GlobalTheory.Tw.Phi n R := by
  ext i j
  simp only [GlobalTheory.Tw.Phi, Matrix.of_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases h : (i : ℕ) + j + 1 = n
  · rw [if_pos h, if_pos (by omega), ← pow_add, show n + 1 + i = j + 2 * (i + 1) by omega, pow_add, pow_mul]
    simp
  · rw [if_neg h, if_neg (by omega), mul_zero]

theorem PhiU_inv_val : ((PhiU n R)⁻¹ : GL (Fin n) R).val = (GlobalTheory.Tw.Phi n R)ᵀ := rfl

theorem invT_invT (g : GL (Fin n) R) : invT n R (invT n R g) = g := by
  apply Units.ext
  show (((invT n R g)⁻¹ : GL (Fin n) R).val)ᵀ = g.val
  rw [← map_inv]
  show (((g⁻¹)⁻¹ : GL (Fin n) R).val)ᵀᵀ = g.val
  rw [inv_inv, transpose_transpose]

theorem map_invT (c : R →+* R) (g : GL (Fin n) R) :
    GeneralLinearGroup.map c (invT n R g) = invT n R (GeneralLinearGroup.map c g) := by
  apply Units.ext
  show c.mapMatrix (((g⁻¹ : GL (Fin n) R).val)ᵀ) = (((GeneralLinearGroup.map c g)⁻¹ : GL (Fin n) R).val)ᵀ
  rw [← map_inv]
  rfl

theorem map_map_self (c : R →+* R) (hc : ∀ x, c (c x) = x) (g : GL (Fin n) R) :
    GeneralLinearGroup.map c (GeneralLinearGroup.map c g) = g :=
  Units.ext (Matrix.ext fun i j => hc (g.val i j))

theorem map_PhiU' (c : R →+* R) : GeneralLinearGroup.map c (PhiU n R) = PhiU n R := by
  apply Units.ext
  ext i j
  change c (GlobalTheory.Tw.Phi n R i j) = GlobalTheory.Tw.Phi n R i j
  simp only [GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

theorem invT_PhiU : invT n R (PhiU n R) = PhiU n R :=
  Units.ext (Matrix.transpose_transpose _)

theorem PhiU_mul_self_val : (PhiU n R * PhiU n R).val = (-1 : R) ^ (n + 1) • (1 : Matrix (Fin n) (Fin n) R) := by
  have h1 : GlobalTheory.Tw.Phi n R * (GlobalTheory.Tw.Phi n R)ᵀ = 1 := Phi_mul_transpose n R
  rw [Phi_transpose', Matrix.mul_smul] at h1
  have hs : ((-1 : R) ^ (n + 1)) * (-1) ^ (n + 1) = 1 := by rw [← mul_pow]; simp
  show GlobalTheory.Tw.Phi n R * GlobalTheory.Tw.Phi n R = _
  calc GlobalTheory.Tw.Phi n R * GlobalTheory.Tw.Phi n R = ((-1 : R) ^ (n + 1) * (-1) ^ (n + 1)) • (GlobalTheory.Tw.Phi n R * GlobalTheory.Tw.Phi n R) := by
        rw [hs, one_smul]
    _ = (-1 : R) ^ (n + 1) • (1 : Matrix (Fin n) (Fin n) R) := by rw [mul_smul, h1]

theorem PhiU_sq_central (g : GL (Fin n) R) : g * (PhiU n R * PhiU n R) = (PhiU n R * PhiU n R) * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul _ g, PhiU_mul_self_val]
  simp

theorem mul_inv_mul_cancel_comm {G : Type} [Group G] (a b P : G) (hP : ∀ g : G, g * (P * P) = (P * P) * g) :
    (a * P * b * P⁻¹)⁻¹ * (a * P) * (b * P * a * P⁻¹) = a * P := by
  have h : (a * P * b * P⁻¹)⁻¹ * (a * P) * (b * P * a * P⁻¹) = (P * P) * a * P⁻¹ := by group
  rw [h, ← hP a]
  group

end Theta

theorem normId : ∀ (R : Type) [CommRing R] (c : R →+* R), (∀ x, c (c x) = x) → ∀ (m : ℕ) (y : GL (Fin m) R),
    ((y * thetaGL m c y).val)ᵀ * (invT m R (y * PhiU m R)).val * c.mapMatrix (y * thetaGL m c y).val =
      (invT m R (y * PhiU m R)).val ∧
    c.mapMatrix (invT m R (y * PhiU m R)).val = (-1 : R) ^ (m - 1) • ((invT m R (y * PhiU m R)).valᵀ * (y * thetaGL m c y).val) := by
  intro R _ c hc m y
  have hth : thetaGL m c y = PhiU m R * invT m R (GeneralLinearGroup.map c y) * (PhiU m R)⁻¹ := rfl
  constructor
  · have ht : ((y * thetaGL m c y).val)ᵀ = (invT m R (y * thetaGL m c y)⁻¹).val := by
      show _ = ((((y * thetaGL m c y)⁻¹)⁻¹ : GL (Fin m) R).val)ᵀ
      rw [inv_inv]
    have hm : c.mapMatrix (y * thetaGL m c y).val = (GeneralLinearGroup.map c (y * thetaGL m c y)).val := rfl
    rw [ht, hm, ← Units.val_mul, ← Units.val_mul]
    congr 1
    rw [hth]
    simp only [map_mul, map_inv, invT_invT, invT_PhiU, map_PhiU', map_invT, map_map_self c hc]
    have := mul_inv_mul_cancel_comm (invT m R y) (GeneralLinearGroup.map c y) (PhiU m R) PhiU_sq_central
    simpa only [mul_assoc] using this
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact Subsingleton.elim _ _
    have h1 : c.mapMatrix (invT m R (y * PhiU m R)).val = (invT m R (GeneralLinearGroup.map c y) * PhiU m R).val := by
      show (GeneralLinearGroup.map c (invT m R (y * PhiU m R))).val = _
      rw [map_invT, map_mul, map_PhiU', map_mul, invT_PhiU]
    have h2 : (invT m R (y * PhiU m R)).valᵀ = ((y * PhiU m R)⁻¹).val := transpose_transpose _
    have h3 : (y * PhiU m R)⁻¹ * (y * thetaGL m c y) = invT m R (GeneralLinearGroup.map c y) * (PhiU m R)⁻¹ := by
      rw [hth]; group
    rw [h1, h2, ← Units.val_mul, h3, Units.val_mul, Units.val_mul, PhiU_inv_val, Phi_transpose', Matrix.mul_smul,
      smul_smul, ← pow_add]
    have : m - 1 + (m + 1) = 2 * m := by omega
    rw [this, pow_mul]
    simp
    rfl

theorem exists_twConj_dlt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ (u : B.A) (Q : (w.adicCompletion E)[X]), Q.Separable → aeval u (Q.map e.symm.toRingHom) = 0 → Algebra.adjoin K.E {u} = ⊤ → ∀ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * ((-1) ^ (m - 1) * u) → (∀ x : B.Aˣ, IsUnit (GlobalTheory.TwLat.gram e b ((β₀ : B.A) * x))) → ∀ y : GLw m w, (nrmL m w y).val.charpoly = Q → ∃ x : B.Aˣ, B.σ (x : B.A) = x ∧ ∃ g : GLw m w, y = g⁻¹ * GlobalTheory.TwLat.dlt e b ((β₀ : B.A) * x) * thL m w g := by
  intro E _ _ _ hE w hw K e he hO hval B m b u Q hQ hu hadj β₀ hβ₀ _ y hy
  have hcc : ∀ z, cj w (cj w z) = z := fun z => by
    obtain ⟨x, rfl⟩ := e.surjective z
    rw [← he, ← he, K.c_c]
  have hth : thL m w = thetaGL m (cj w) := by rw [thL, if_neg hw]
  have hnr : nrmL m w y = y * thetaGL m (cj w) y := by rw [nrmL, if_neg hw]

  have huu : u * B.σ u = 1 := by
    have h := congrArg B.σ hβ₀
    rw [B.σ_σ, map_mul, hβ₀, map_mul, map_pow, map_neg, map_one] at h
    have hε : ((-1 : B.A) ^ (m - 1)) * (-1) ^ (m - 1) = 1 := by rw [← mul_pow]; simp
    have h2 : (β₀ : B.A) * (u * B.σ u) = β₀ * 1 := by
      linear_combination (-1 : B.A) * h - ((β₀ : B.A) * u * B.σ u) * hε
    exact (Units.mul_right_inj β₀).1 h2

  have hQm : Q.Monic := hy ▸ Matrix.charpoly_monic _
  have hQd : Q.natDegree = m := by rw [← hy, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hfin : Module.finrank K.E B.A = Q.natDegree := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin, hQd]
  have hcp := GlobalTheory.T.charpoly_mulLeft_generator_eq_map_symm K B _ e u Q hQm hadj hu hfin
  have hU : (GlobalTheory.TwLat.mulMat e b u).charpoly = Q := by
    have : GlobalTheory.TwLat.mulMat e b u = (LinearMap.toMatrix b b (LinearMap.mulLeft K.E u)).map (e : K.E →+* w.adicCompletion E) := rfl
    rw [this, Matrix.charpoly_map, LinearMap.charpoly_toMatrix, hcp, Polynomial.map_map]
    have hid : (e : K.E →+* w.adicCompletion E).comp e.symm.toRingHom = RingHom.id _ := by
      ext z; simp
    rw [hid, Polynomial.map_id]

  let B' : GlobalTheory.UnitLemma.InvAlg K := { B with g := u }
  have hP' : B'.P.Separable := by
    show (LinearMap.mulLeft K.E u).charpoly.Separable
    rw [hcp]; exact hQ.map
  have hnd : (Algebra.traceForm K.E B.A).Nondegenerate := GlobalTheory.UnitLemma.Sandwich.traceForm_nondegenerate B' hP'

  obtain ⟨P, hP⟩ := GlobalTheory.T.conj_of_charpoly_eq_of_charpoly_separable _ m (nrmL m w y).val (GlobalTheory.TwLat.mulMat e b u) (by rw [hy, hU]) (by rw [hy]; exact hQ)
  rw [hnr] at hP
  obtain ⟨hn1, hn2⟩ := normId _ (cj w) hcc m y
  set N := (y * thetaGL m (cj w) y).val with hN
  set U := GlobalTheory.TwLat.mulMat e b u with hUdef
  set Gy := (invT m _ (y * PhiU m _)).val with hGy
  set cm := (cj w).mapMatrix (m := Fin m) with hcm
  let Gu : GLw m w := invT m _ P⁻¹ * invT m _ (y * PhiU m _) * GeneralLinearGroup.map (cj w) P
  have hPt : (invT m _ P⁻¹).val = P.valᵀ := by
    show ((P⁻¹)⁻¹ : GLw m w).valᵀ = _
    rw [inv_inv]
  have hGu : Gu.val = P.valᵀ * Gy * cm P.val := by
    show (invT m _ P⁻¹).val * Gy * cm P.val = _
    rw [hPt]
  have h1 : Uᵀ * P.valᵀ = P.valᵀ * Nᵀ := by rw [← transpose_mul, ← transpose_mul, hP]
  have h2 : cm P.val * cm U = cm N * cm P.val := by rw [← map_mul, ← map_mul, hP]
  have hinv : Uᵀ * Gu.val * cm U = Gu.val := by
    rw [hGu]
    calc Uᵀ * (P.valᵀ * Gy * cm P.val) * cm U = (Uᵀ * P.valᵀ) * Gy * (cm P.val * cm U) := by
          simp only [Matrix.mul_assoc]
      _ = P.valᵀ * (Nᵀ * Gy * cm N) * cm P.val := by rw [h1, h2]; simp only [Matrix.mul_assoc]
      _ = P.valᵀ * Gy * cm P.val := by rw [hn1]
  obtain ⟨β, hβ⟩ := GlobalTheory.T.exists_traceForm_of_unitaryGenerator_invariant_form E w K e he B m b u hadj huu hnd Gu.val hinv
  have hsym : cm (GlobalTheory.TwLat.gram e b β) = (-1 : w.adicCompletion E) ^ (m - 1) • ((GlobalTheory.TwLat.gram e b β)ᵀ * U) := by
    rw [hβ, hGu, map_mul, map_mul, hn2]
    have hcP : cm (P.valᵀ) = (cm P.val)ᵀ := rfl
    have hcc' : cm (cm P.val) = P.val := Matrix.ext fun i j => hcc (P.val i j)
    rw [hcP, hcc', transpose_mul, transpose_mul, transpose_transpose, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    simp only [Matrix.mul_assoc, hP]
  have hGunit : IsUnit (GlobalTheory.TwLat.gram e b β) := hβ ▸ Gu.isUnit
  obtain ⟨hσβ, hβu⟩ := GlobalTheory.T.traceFormGram_asymmetry_forces_beta_relation E w K e he B m b u β hnd hGunit hsym
  refine ⟨β₀⁻¹ * hβu.unit, ?_, P⁻¹, ?_⟩
  · have hi : (((β₀⁻¹ : B.Aˣ) : B.A)) * β₀ = 1 := by simp
    have hi' : B.σ (β₀ : B.A) * B.σ ((β₀⁻¹ : B.Aˣ) : B.A) = 1 := by rw [← map_mul]; simp
    rw [hβ₀] at hi'
    simp only [Units.val_mul, IsUnit.unit_spec, map_mul, hσβ]
    linear_combination (β * ((β₀⁻¹ : B.Aˣ) : B.A)) * hi' - (β * B.σ ((β₀⁻¹ : B.Aˣ) : B.A) * ((-1) ^ (m - 1) * u)) * hi
  · have hb : (β₀ : B.A) * ((β₀⁻¹ * hβu.unit : B.Aˣ) : B.A) = β := by simp
    rw [hb, GlobalTheory.TwLat.dlt, dif_pos hGunit, hth]
    have hGe : hGunit.unit = Gu := Units.ext (by rw [IsUnit.unit_spec, hβ])
    rw [hGe]
    have hII : ∀ g : GLw m w, invT m _ (invT m _ g) = g := fun g => by
      apply Units.ext
      show (((invT m _ g)⁻¹ : GLw m w).val)ᵀ = g.val
      rw [← map_inv]
      show (((g⁻¹)⁻¹ : GLw m w).val)ᵀᵀ = g.val
      rw [inv_inv, transpose_transpose]
    have hth' : ∀ g : GLw m w, thetaGL m (cj w) g = PhiU m _ * invT m _ (GeneralLinearGroup.map (cj w) g) * (PhiU m _)⁻¹ :=
      fun g => rfl
    show y = P⁻¹⁻¹ * (invT m _ (invT m _ P⁻¹ * invT m _ (y * PhiU m _) * GeneralLinearGroup.map (cj w) P) * (PhiU m _)⁻¹) *
      thetaGL m (cj w) P⁻¹
    rw [hth', map_mul, map_mul, hII, hII, map_inv, map_inv]
    group

end GlobalTheory.TwLat.ClSurj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryModelOfSelfDualLatticeCountNeZero
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

noncomputable section

namespace GlobalTheory.KapLat

theorem exists_orthonormal_of_selfDual (K : GlobalTheory.UnitLemma.UQ) (V : Type) [AddCommGroup V] [Module K.E V]
    [Module K.O V] [IsScalarTower K.O K.E V] [FiniteDimensional K.E V] (h : V → V → K.E)
    (hadd : ∀ y y' z, h (y + y') z = h y z + h y' z) (hsmul : ∀ (a : K.E) y z, h (a • y) z = a * h y z)
    (hsym : ∀ y z, h z y = K.c (h y z)) (L : Submodule K.O V) (hfg : L.FG)
    (hsp : Submodule.span K.E (L : Set V) = ⊤) (hsd : ∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) :
    ∃ b : Module.Basis (Fin (Module.finrank K.E V)) K.E V, ∀ i j, h (b i) (b j) = if i = j then 1 else 0 := by
  have key : ∀ k, k ≤ Module.finrank K.E V → ∃ f : Fin k → V, (∀ i, f i ∈ L) ∧
      (∀ i j, i ≠ j → h (f i) (f j) = 0) ∧ ∀ i, ∃ t : K.O, IsUnit t ∧ h (f i) (f i) = algebraMap K.O K.E t := by
    intro k
    induction k with
    | zero => intro _; exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    | succ k ih =>
      intro hk
      obtain ⟨f, hfL, hfo, hfu⟩ := ih (by omega)
      obtain ⟨y, hyL, hyo, hyu⟩ := GlobalTheory.T.selfDual_lattice_orthogonal_unit_norm_extension K V h hadd hsmul hsym L hfg hsp hsd k f hfL hfo hfu (by omega)
      refine ⟨Fin.snoc f y, ?_, ?_, ?_⟩
      · intro i
        induction i using Fin.lastCases with
        | last => simpa using hyL
        | cast i => simpa using hfL i
      · intro i j hij
        induction i using Fin.lastCases with
        | last =>
          induction j using Fin.lastCases with
          | last => exact absurd rfl hij
          | cast j => simpa using hyo j
        | cast i =>
          induction j using Fin.lastCases with
          | last => simp only [Fin.snoc_castSucc, Fin.snoc_last]; rw [hsym, hyo i, map_zero]
          | cast j =>
            simp only [Fin.snoc_castSucc]
            exact hfo i j fun e => hij (by rw [e])
      · intro i
        induction i using Fin.lastCases with
        | last => simpa using hyu
        | cast i => simpa using hfu i
  obtain ⟨f, -, hfo, hfu⟩ := key _ le_rfl
  choose t ht hft using hfu
  choose v hv using fun i => GlobalTheory.T.fixed_integral_unit_eq_norm_unramified K (t i) (ht i) (by rw [← hft, ← hsym])
  have hsmul2 : ∀ (a : K.E) y z, h y (a • z) = K.c a * h y z := by
    intro a y z
    rw [hsym, hsmul, map_mul, hsym z y]
  have ht0 : ∀ i, algebraMap K.O K.E (t i) ≠ 0 := fun i =>
    (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 (ht i).ne_zero
  have hv0 : ∀ i, v i ≠ 0 := by
    intro i h0
    apply ht0 i
    rw [← hv i, h0, zero_mul]
  let g : Fin (Module.finrank K.E V) → V := fun i => (v i)⁻¹ • f i
  have hg : ∀ i j, h (g i) (g j) = if i = j then 1 else 0 := by
    intro i j
    simp only [g, hsmul, hsmul2]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, hft, ← hv i, map_inv₀]
      have : K.c (v i) ≠ 0 := by simpa using hv0 i
      field_simp
      exact div_self (hv0 i)
    · rw [if_neg hij, hfo i j hij, mul_zero, mul_zero]
  let φ : V → V →ₗ[K.E] K.E := fun z =>
    { toFun := fun y => h y z
      map_add' := fun y y' => hadd y y' z
      map_smul' := fun a y => by simp [hsmul] }
  have hli : LinearIndependent K.E g := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have := congrArg (φ (g i)) hc
    simp only [map_sum, map_smul, map_zero] at this
    simpa [φ, hg] using this
  refine ⟨Module.Basis.mk hli (hli.span_eq_top_of_card_eq_finrank' (by simp)).ge, fun i j => ?_⟩
  rw [Module.Basis.mk_apply, Module.Basis.mk_apply]
  exact hg i j

theorem X_nonempty_of_N_ne_zero {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (hN : B.N x ≠ 0) :
    (B.X x).Nonempty := by
  by_contra hX
  rw [Set.not_nonempty_iff_eq_empty] at hX
  apply hN
  haveI : IsEmpty (GlobalTheory.UnitLemma.Orb K.O B.T (B.X x)) :=
    ⟨fun o => by
      induction o using Quot.ind with
      | mk L => exact Set.eq_empty_iff_forall_notMem.1 hX L.1 L.2⟩
  unfold GlobalTheory.UnitLemma.InvAlg.N GlobalTheory.UnitLemma.orbSum
  exact finsum_of_isEmpty _

theorem exists_model_of_N_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (n : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A), Fits w e B Q u → Q.natDegree = n → B.σ x = x → IsUnit x → B.N x ≠ 0 → ∃ γ : GLw n w, γ ∈ UL n w ∧ IsModel w e B u x γ := by
  intro E _ _ _ w hw K e hB n Q B u x hF hn hσx _ hN
  obtain ⟨L, hlat, -, hsd⟩ := X_nonempty_of_N_ne_zero B x hN
  obtain ⟨b, hb⟩ := exists_orthonormal_of_selfDual K B.A (B.herm x)
    (fun y y' z => by unfold GlobalTheory.UnitLemma.InvAlg.herm; rw [mul_add, add_mul, map_add])
    (fun a y z => GlobalTheory.UnitLemma.Basic.herm_smul_left B x y z a)
    (fun y z => GlobalTheory.UnitLemma.Basic.herm_symm B x hσx y z) L hlat.1 hlat.2 hsd
  have hd : Module.finrank K.E B.A = n := hF.2.2.1.trans hn
  refine GlobalTheory.T.exists_hermitianModel_of_orthonormal_basis E w hw K e hB n B u x hF.2.2.2 (b.reindex (finCongr hd)) fun i j => ?_
  simp only [Module.Basis.reindex_apply, hb, EmbeddingLike.apply_eq_iff_eq]

end GlobalTheory.KapLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightPreservingPartNonLoweringUnit
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact

namespace GlobalTheory.WeightPart

variable {S ι : Type} [Ring S] [Fintype ι] {ε : ι → S} {w : ι → ℤ}

def dg (ε : ι → S) (w : ι → ℤ) (x : S) : S := ∑ a, ∑ b, if w a = w b then ε a * x * ε b else 0

theorem ext_sand (he : CompleteOrthogonalIdempotents ε) {x y : S} (h : ∀ a b, ε a * x * ε b = ε a * y * ε b) : x = y := by
  have e : ∀ z : S, z = ∑ a, ∑ b, ε a * z * ε b := fun z => by
    simp only [← Finset.mul_sum, ← Finset.sum_mul, he.complete, mul_one, one_mul]
  rw [e x, e y]
  simp only [h]

theorem sand_mul (he : CompleteOrthogonalIdempotents ε) (x y : S) (a b : ι) :
    ε a * (x * y) * ε b = ∑ c, (ε a * x * ε c) * (ε c * y * ε b) := by
  have e : ∀ c, (ε a * x * ε c) * (ε c * y * ε b) = ε a * x * ε c * (y * ε b) := fun c => by
    rw [mul_assoc (ε c) y, ← mul_assoc _ (ε c) (y * ε b), mul_assoc _ (ε c) (ε c), (he.idem c).eq]
  simp only [e]
  rw [← Finset.sum_mul, ← Finset.mul_sum, he.complete]
  simp only [mul_one, mul_assoc]

theorem sand_dg (he : CompleteOrthogonalIdempotents ε) (x : S) (a b : ι) :
    ε a * dg ε w x * ε b = if w a = w b then ε a * x * ε b else 0 := by
  classical
  rw [dg, Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single a, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_eq_single b]
  · split_ifs
    · rw [← mul_assoc, ← mul_assoc, (he.idem a).eq, mul_assoc _ (ε b), (he.idem b).eq]
    · simp
  · intro c _ hc
    split_ifs
    · rw [mul_assoc, mul_assoc _ (ε c), he.ortho hc, mul_zero, mul_zero]
    · simp
  · simp
  · intro c _ hc
    rw [Finset.mul_sum, Finset.sum_eq_zero, zero_mul]
    intro d _
    split_ifs
    · rw [← mul_assoc, ← mul_assoc, he.ortho hc.symm, zero_mul, zero_mul]
    · simp
  · simp

theorem dg_mul_dg (he : CompleteOrthogonalIdempotents ε) {x y : S} (h : x * y = 1)
    (hx : ∀ a b, w a < w b → ε a * x * ε b = 0) (hy : ∀ a b, w a < w b → ε a * y * ε b = 0) :
    dg ε w x * dg ε w y = 1 := by
  refine ext_sand he fun a b => ?_
  by_cases hab : w a = w b
  · rw [← h, sand_mul he, sand_mul he]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [sand_dg he, sand_dg he]
    rcases lt_trichotomy (w a) (w c) with h1 | h1 | h1
    · rw [if_neg h1.ne, hx a c h1, zero_mul, zero_mul]
    · rw [if_pos h1, if_pos (h1 ▸ hab)]
    · rw [if_neg h1.ne', hy c b (hab ▸ h1), zero_mul, mul_zero]
  · rw [mul_one, he.ortho (fun e => hab (congrArg w e)), sand_mul he]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [sand_dg he, sand_dg he]
    by_cases h1 : w a = w c
    · rw [if_neg (show ¬ w c = w b from h1 ▸ hab), mul_zero]
    · rw [if_neg h1, zero_mul]

theorem exists_weightPart : ∀ {S ι : Type} [Ring S] [Fintype ι] (st : S →+ S) (ε : ι → S) (w : ι → ℤ) (τ : ι → ι), (∀ x y, st (x * y) = st y * st x) → (∀ x, st (st x) = x) → CompleteOrthogonalIdempotents ε → (∀ a, st (ε a) = ε (τ a)) → (∀ a, w (τ a) = -w a) → (∀ a, τ (τ a) = a) → ∀ x y : S, x * y = 1 → y * x = 1 → st x = y → (∀ a b, w a < w b → ε a * x * ε b = 0) → (∀ a b, w a < w b → ε a * y * ε b = 0) → ∃ m m' : S, m * m' = 1 ∧ m' * m = 1 ∧ st m = m' ∧ (∀ a b, w a ≠ w b → ε a * m * ε b = 0) ∧ (∀ a b, w a ≠ w b → ε a * m' * ε b = 0) ∧ x * m' - 1 ∈ raise ε w 0 ∧ ∀ S₀ : Subring S, (∀ a, ε a ∈ S₀) → x ∈ S₀ → y ∈ S₀ → m ∈ S₀ ∧ m' ∈ S₀ := by
  intro S ι _ _ st ε w τ hst hss he hε hw hτ x y hxy hyx hs hx hy
  have hm : ∀ z a b, w a ≠ w b → ε a * dg ε w z * ε b = 0 := fun z a b h => by rw [sand_dg he, if_neg h]
  have h1 := dg_mul_dg he hxy hx hy
  refine ⟨dg ε w x, dg ε w y, h1, dg_mul_dg he hyx hy hx, ?_, hm x, hm y, ?_, ?_⟩
  · have key : ∀ z a b, ε a * st z * ε b = st (ε (τ b) * z * ε (τ a)) := fun z a b => by
      rw [hst, hst, hε, hε, hτ, hτ, mul_assoc]
    refine ext_sand he fun a b => ?_
    rw [key, sand_dg he, sand_dg he, ← hs, key, hw, hw]
    by_cases h : w a = w b
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun e => h (neg_inj.1 e).symm), map_zero]
  · intro a b hab
    have hab' : w a ≤ w b := by simpa using hab
    rw [← h1, ← sub_mul, sand_mul he]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases h : w c = w b
    · rw [mul_sub, sub_mul, sand_dg he]
      split_ifs with h2
      · rw [sub_self, zero_mul]
      · rw [hx a c (lt_of_le_of_ne (h ▸ hab') h2), sub_self, zero_mul]
    · rw [hm y c b h, mul_zero]
  · intro S₀ h0 hx0 hy0
    have : ∀ z ∈ S₀, dg ε w z ∈ S₀ := fun z hz =>
      sum_mem fun a _ => sum_mem fun b _ => by
        split_ifs
        · exact mul_mem (mul_mem (h0 a) hz) (h0 b)
        · exact zero_mem _
    exact ⟨this x hx0, this y hy0⟩

end GlobalTheory.WeightPart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPtHomApply
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TraceBlocks

section Generic

variable {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]

def eqvM (ι : H →* G) (ρ : Representation ℂ H V) (K : Subgroup G) : Submodule ℂ (G → V) where
  carrier := {φ | (∀ h x, φ (ι h * x) = ρ h (φ x)) ∧ ∀ k ∈ K, ∀ x, φ (x * k) = φ x}
  add_mem' := by
    intro a b ha hb
    refine ⟨fun h x => ?_, fun k hk x => ?_⟩
    · simp only [Pi.add_apply, ha.1 h x, hb.1 h x, map_add]
    · simp only [Pi.add_apply, ha.2 k hk x, hb.2 k hk x]
  zero_mem' := ⟨fun _ _ => by simp, fun _ _ _ => rfl⟩
  smul_mem' := by
    intro c a ha
    refine ⟨fun h x => ?_, fun k hk x => ?_⟩
    · simp only [Pi.smul_apply, ha.1 h x, map_smul]
    · simp only [Pi.smul_apply, ha.2 k hk x]

def stabCard (ι : H →* G) (K : Subgroup G) (x : G) : ℕ :=
  Nat.card (ι.range ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G)

def secM (ι : H →* G) (ρ : Representation ℂ H V) (K : Subgroup G) (x : G) : V →ₗ[ℂ] (G → V) where
  toFun v y := ((stabCard ι K x : ℂ))⁻¹ • (∑ᶠ h : H, if (ι h * x)⁻¹ * y ∈ K then ρ h else 0) v
  map_add' a b := by
    funext y
    simp only [map_add, smul_add, Pi.add_apply]
  map_smul' c a := by
    funext y
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_comm c]

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def finPtHom : UE E n →* finU E n where
  toFun := finPt
  map_one' := by
    apply Subtype.ext
    rw [FinPtLoc.finPt_eq]
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, FinPtLoc.finPt_eq, FinPtLoc.finPt_eq, FinPtLoc.finPt_eq]
    apply Subtype.ext
    exact (congrArg (finGL E n) (map_mul (ratF E n) a.1 b.1)).trans (map_mul _ _ _)

theorem finPtHom_apply (γ : UE E n) : finPtHom γ = finPt γ := rfl

theorem wAt_mul (lam : InfinitePlace E → DomWeight n) (a b : UE E n) :
    GlobalTheory.BCT.TrKer.wAt lam (a * b) = GlobalTheory.BCT.TrKer.wAt lam a ∘ₗ GlobalTheory.BCT.TrKer.wAt lam b := by
  unfold GlobalTheory.BCT.TrKer.wAt
  rw [← PiTensorProduct.map_comp]
  refine congrArg PiTensorProduct.map (funext fun v => ?_)
  change GlobalTheory.Branching.sqRep ℂ n (lam v) (GeneralLinearGroup.map v.embedding (a.1 * b.1)) = _
  rw [map_mul, map_mul, Module.End.mul_eq_comp]

theorem wAt_one (lam : InfinitePlace E → DomWeight n) : GlobalTheory.BCT.TrKer.wAt lam 1 = LinearMap.id := by
  unfold GlobalTheory.BCT.TrKer.wAt
  simp only [OneMemClass.coe_one, map_one]
  exact PiTensorProduct.map_id

def wDual (lam : InfinitePlace E → DomWeight n) : Representation ℂ (UE E n) (Module.Dual ℂ (GlobalTheory.BCT.TrKer.Wsp lam)) where
  toFun γ := (GlobalTheory.BCT.TrKer.wAt lam γ⁻¹).dualMap
  map_one' := by
    rw [inv_one, wAt_one]
    rfl
  map_mul' a b := by
    rw [_root_.mul_inv_rev, wAt_mul, ← LinearMap.dualMap_comp_dualMap]
    rfl

end GlobalTheory.BCT.TraceBlocks
end
end

