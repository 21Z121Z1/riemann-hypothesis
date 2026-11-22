import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0049
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0062
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0089
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0087
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0085
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0083
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0035
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0081
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0082
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussSumHermitianNormLevelOne
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

namespace GlobalTheory.CompanionTheory.SiegLoc.GaussOne

variable {E : Type} [CommRing E] [Fintype E] {τ : E →+* E} {q : ℕ} {ε : ℤ}

open Classical in

theorem sum_fixed_eq_zero (χ : AddChar E ℂ) (A b : E) (hb : τ b = b) (hχ : χ (A * b) ≠ 1) :
    ∑ t ∈ Finset.univ.filter (fun t : E => τ t = t), χ (A * t) = 0 := by
  set S := ∑ t ∈ Finset.univ.filter (fun t : E => τ t = t), χ (A * t) with hS
  have key : χ (A * b) * S = S := by
    rw [hS, Finset.mul_sum]
    refine Finset.sum_nbij' (fun t => t + b) (fun t => t - b) ?_ ?_ ?_ ?_ ?_
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      rw [map_add, ht, hb]
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      rw [map_sub, ht, hb]
    · intro t _
      simp
    · intro t _
      simp
    · intro t _
      rw [← AddChar.map_add_eq_mul, mul_add, add_comm]
  have h1 : (1 - χ (A * b)) * S = 0 := by rw [sub_mul, one_mul, key, sub_self]
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hχ
  · exact h

open Classical in

theorem card_filter_norm (t : E) :
    (((Finset.univ.filter (fun w : E => τ w * w = t)).card : ℕ) : ℤ) =
      (Nat.card {a : E // a * τ a = t} : ℤ) := by
  have hf : Finset.univ.filter (fun w : E => τ w * w = t) =
      Finset.univ.filter (fun a : E => a * τ a = t) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [mul_comm]
  rw [hf, Nat.card_eq_fintype_card, Fintype.card_subtype]

open Classical in

theorem gauss_core (h : ResAlg E τ q ε) (χ : AddChar E ℂ) (A b : E) (hb : τ b = b)
    (hχ : χ (A * b) ≠ 1) :
    ∑ w : E, χ (A * (τ w * w)) = (ε : ℂ) * q := by
  have hmap : ∀ w ∈ (Finset.univ : Finset E),
      τ w * w ∈ Finset.univ.filter (fun t : E => τ t = t) := by
    intro w _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_mul, h.inv]
    exact mul_comm _ _
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  have hfib : ∀ t ∈ Finset.univ.filter (fun t : E => τ t = t),
      (∑ w ∈ Finset.univ.filter (fun w : E => τ w * w = t), χ (A * (τ w * w))) =
        (((q : ℂ) - ε) + if t = 0 then (q : ℂ) * ε else 0) * χ (A * t) := by
    intro t ht
    have ht' : τ t = t := (Finset.mem_filter.mp ht).2
    rw [Finset.sum_congr rfl (fun w hw => by rw [(Finset.mem_filter.mp hw).2]), Finset.sum_const,
      nsmul_eq_mul]
    congr 1
    have hc := card_filter_norm (τ := τ) t
    have hc' : (((Finset.univ.filter (fun w : E => τ w * w = t)).card : ℕ) : ℂ) =
        ((Nat.card {a : E // a * τ a = t} : ℤ) : ℂ) := by
      rw [← hc]
      push_cast
      rfl
    rw [hc']
    by_cases h0 : t = 0
    · subst h0
      rw [GlobalTheory.T.norm_fibre_card_zero E τ q ε h, if_pos rfl]
      push_cast
      ring
    · rw [GlobalTheory.T.norm_fibre_card_nonzero E τ q ε h t ht' h0, if_neg h0]
      push_cast
      ring
  rw [Finset.sum_congr rfl hfib]
  simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_fixed_eq_zero χ A b hb hχ, mul_zero, zero_add]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and,
    map_zero, if_true, mul_zero, AddChar.map_zero_eq_one, mul_one]
  ring

end GlobalTheory.CompanionTheory.SiegLoc.GaussOne

namespace GlobalTheory.CompanionTheory.SiegLoc

theorem gauss_level_one : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ)
    (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)] (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ),
    IsLevelChars σ ϖ ψ → ∀ (a : R), σ a = a → a ∉ lev ϖ 1 →
    (∑ w : R ⧸ lev ϖ 1, ψ 1 (Ideal.Quotient.mk (lev ϖ 1) a * (barσ σ ϖ hR.fix_ϖ 1 w * w))) =
      (ε : ℂ) * q := by
  intro R _ σ ϖ q ε hR _ ψ hψ a ha hna
  have hex : ∃ b, σ b = b ∧ ψ 1 (Ideal.Quotient.mk _ (a * b)) ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact hna (hψ.prim a ha hcon)
  obtain ⟨b, hb, hχ⟩ := hex
  refine GaussOne.gauss_core (GlobalTheory.T.residue_algebra_unramified R σ ϖ q ε hR) (ψ 1) _ (Ideal.Quotient.mk _ b) ?_ ?_
  · rw [barσ_mk, hb]
  · rwa [← map_mul]

end GlobalTheory.CompanionTheory.SiegLoc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCharacterOrthogonality
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

namespace GlobalTheory.CompanionTheory.SiegLoc.HermOrth

variable {R : Type} [CommRing R]

theorem red_add' (ϖ : R) (k : ℕ) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R) :
    red ϖ k (x + y) = red ϖ k x + red ϖ k y := by
  ext i j
  simp [red]

theorem red_neg' (ϖ : R) (k : ℕ) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) :
    red ϖ k (-x) = -red ϖ k x := by
  ext i j
  simp [red]

theorem cT_add' (σ : R →+* R) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R) :
    cT σ (x + y) = cT σ x + cT σ y := by
  ext i j
  simp [cT]

theorem cT_neg' (σ : R →+* R) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) :
    cT σ (-x) = -cT σ x := by
  ext i j
  simp [cT]

theorem cT_single' (σ : R →+* R) {n : ℕ} (i j : Fin n) (c : R) :
    cT σ (Matrix.single i j c) = Matrix.single j i (σ c) := by
  simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.map_single, Matrix.transpose_single]

theorem trace_single_mul' {n : ℕ} (i j : Fin n) (c : R) (y : Matrix (Fin n) (Fin n) R) :
    Matrix.trace (Matrix.single i j c * y) = c * y j i := by
  rw [Matrix.trace_single_mul, smul_eq_mul]

theorem trace_red_mul (ϖ : R) (k n : ℕ) (b y : Matrix (Fin n) (Fin n) R) :
    Matrix.trace (red ϖ k b * red ϖ k y) = Ideal.Quotient.mk (lev ϖ k) (Matrix.trace (b * y)) := by
  unfold PositivityTheory.PfSWUS.Loc.red
  rw [← Matrix.map_mul]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.map_apply, map_sum]

theorem tsum_eq_zero_of_shift {G : Type} [AddCommGroup G] (H : Set G)
    (hadd : ∀ a b, a ∈ H → b ∈ H → a + b ∈ H) (hneg : ∀ a, a ∈ H → -a ∈ H)
    (f : G → ℂ) (hf : ∀ a b, f (a + b) = f a * f b) (B₀ : G) (hB₀ : B₀ ∈ H) (h : f B₀ ≠ 1) :
    ∑' B : H, f B.1 = 0 := by
  let e : H ≃ H :=
    { toFun := fun B => ⟨B₀ + B.1, hadd _ _ hB₀ B.2⟩
      invFun := fun B => ⟨-B₀ + B.1, hadd _ _ (hneg _ hB₀) B.2⟩
      left_inv := fun B => Subtype.ext (by simp)
      right_inv := fun B => Subtype.ext (by simp) }
  have key : ∑' B : H, f B.1 = f B₀ * ∑' B : H, f B.1 := by
    calc ∑' B : H, f B.1 = ∑' B : H, f (e B).1 := (e.tsum_eq (fun B : H => f B.1)).symm
      _ = ∑' B : H, f B₀ * f B.1 := tsum_congr fun B => by
          show f (B₀ + B.1) = _
          exact hf _ _
      _ = f B₀ * ∑' B : H, f B.1 := tsum_mul_left
  have hzero : (f B₀ - 1) * ∑' B : H, f B.1 = 0 := by
    rw [sub_mul, one_mul, ← key, sub_self]
  rcases mul_eq_zero.mp hzero with h' | h'
  · exact absurd (sub_eq_zero.mp h') h
  · exact h'

theorem hermMod_add {σ : R →+* R} {ϖ : R} {n k : ℕ}
    (a b : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) (ha : a ∈ hermMod σ ϖ n k)
    (hb : b ∈ hermMod σ ϖ n k) : a + b ∈ hermMod σ ϖ n k := by
  unfold PositivityTheory.PfSWUS.Loc.hermMod at ha hb ⊢
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  have ha'' : PositivityTheory.PfSWUS.Loc.cT σ a' = a' := ha'
  have hb'' : PositivityTheory.PfSWUS.Loc.cT σ b' = b' := hb'
  refine ⟨a' + b', ?_, GlobalTheory.CompanionTheory.SiegLoc.HermOrth.red_add' _ _ _ _⟩
  show PositivityTheory.PfSWUS.Loc.cT σ (a' + b') = a' + b'
  rw [GlobalTheory.CompanionTheory.SiegLoc.HermOrth.cT_add', ha'', hb'']

theorem hermMod_neg {σ : R →+* R} {ϖ : R} {n k : ℕ}
    (a : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) (ha : a ∈ hermMod σ ϖ n k) :
    -a ∈ hermMod σ ϖ n k := by
  unfold PositivityTheory.PfSWUS.Loc.hermMod at ha ⊢
  obtain ⟨a', ha', rfl⟩ := ha
  have ha'' : PositivityTheory.PfSWUS.Loc.cT σ a' = a' := ha'
  refine ⟨-a', ?_, GlobalTheory.CompanionTheory.SiegLoc.HermOrth.red_neg' _ _ _⟩
  show PositivityTheory.PfSWUS.Loc.cT σ (-a') = -a'
  rw [GlobalTheory.CompanionTheory.SiegLoc.HermOrth.cT_neg', ha'']

theorem red_eq_zero_of_trivial {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ}
    {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ} (hR : IsUnrQuad R σ ϖ q ε) (hψ : IsLevelChars σ ϖ ψ)
    (n k : ℕ) (y : Matrix (Fin n) (Fin n) R) (hy : cT σ y = y)
    (h : ∀ b : Matrix (Fin n) (Fin n) R, cT σ b = b →
      ψ k (Ideal.Quotient.mk _ (Matrix.trace (b * y))) = 1) :
    red ϖ k y = 0 := by
  have hσσ : ∀ a, σ (σ a) = a := hR.1
  ext i j
  simp only [PositivityTheory.PfSWUS.Loc.red, Matrix.map_apply, Matrix.zero_apply]
  rw [Ideal.Quotient.eq_zero_iff_mem]
  apply GlobalTheory.CompanionTheory.SiegLoc.trace_nondeg hR hψ k (y i j)
  intro t
  have hyji : σ (y i j) = y j i := by
    have hentry := congrFun (congrFun hy j) i
    simpa [PositivityTheory.PfSWUS.Loc.cT] using hentry
  have hb : PositivityTheory.PfSWUS.Loc.cT σ (Matrix.single j i t + Matrix.single i j (σ t)) =
      Matrix.single j i t + Matrix.single i j (σ t) := by
    rw [GlobalTheory.CompanionTheory.SiegLoc.HermOrth.cT_add', GlobalTheory.CompanionTheory.SiegLoc.HermOrth.cT_single', GlobalTheory.CompanionTheory.SiegLoc.HermOrth.cT_single',
      hσσ, add_comm]
  have htr := h _ hb
  rw [Matrix.add_mul, Matrix.trace_add, GlobalTheory.CompanionTheory.SiegLoc.HermOrth.trace_single_mul',
    GlobalTheory.CompanionTheory.SiegLoc.HermOrth.trace_single_mul'] at htr
  rw [map_mul σ, hyji]
  exact htr

theorem orth_hermMod (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ)
    (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)]
    (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ) (hψ : IsLevelChars σ ϖ ψ) (n k : ℕ)
    (Y : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) (hY : Y ∈ hermMod σ ϖ n k) :
    (Y = 0 → (∑' B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * Y))) =
        (Nat.card (hermMod σ ϖ n k) : ℂ)) ∧
      (Y ≠ 0 → (∑' B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * Y))) = 0) := by
  refine ⟨fun h0 => ?_, fun hne => ?_⟩
  · subst h0
    simp only [Matrix.mul_zero, Matrix.trace_zero, AddChar.map_zero_eq_one]
    rw [tsum_const, nsmul_eq_mul, mul_one]
  · have hY' := hY
    unfold PositivityTheory.PfSWUS.Loc.hermMod at hY'
    obtain ⟨y, hy, rfl⟩ := hY'
    by_contra hsum
    apply hne
    apply GlobalTheory.CompanionTheory.SiegLoc.HermOrth.red_eq_zero_of_trivial hR hψ n k y hy
    intro b hb
    rw [← GlobalTheory.CompanionTheory.SiegLoc.HermOrth.trace_red_mul]
    by_contra hb1
    exact hsum (GlobalTheory.CompanionTheory.SiegLoc.HermOrth.tsum_eq_zero_of_shift _
      (fun a₁ a₂ h₁ h₂ => GlobalTheory.CompanionTheory.SiegLoc.HermOrth.hermMod_add a₁ a₂ h₁ h₂)
      (fun a₁ h₁ => GlobalTheory.CompanionTheory.SiegLoc.HermOrth.hermMod_neg a₁ h₁)
      (fun B => ψ k (Matrix.trace (B * PositivityTheory.PfSWUS.Loc.red ϖ k y)))
      (fun a₁ a₂ => by simp only [Matrix.add_mul, Matrix.trace_add, AddChar.map_add_eq_mul])
      (PositivityTheory.PfSWUS.Loc.red ϖ k b) ⟨b, hb, rfl⟩ hb1)

end GlobalTheory.CompanionTheory.SiegLoc.HermOrth
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianVectorValuesCard
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens.Sphere

theorem card_fibre {E : Type} [CommRing E] {τ : E →+* E} [Fintype E] {V : Type} [AddCommGroup V]
    [Module E V] [Finite V] (B : HermSp E τ V) {w : V} (hw : IsUnit (B.h w w)) (c : E) :
    Nat.card {v : V // B.h v v = c} =
      ∑ a : E, Nat.card {v : B.perp w // (B.perpForm hw).h v v = c - a * τ a * B.h w w} := by
  rw [← Nat.card_sigma]
  refine Nat.card_congr ?_
  have e1 : {x : E × B.perp w // (B.perpForm hw).h x.2 x.2 = c - x.1 * τ x.1 * B.h w w} ≃
      {v : V // B.h v v = c} :=
    Equiv.subtypeEquiv (B.perpEquiv hw) (by
      rintro ⟨a, v⟩
      have hv : B.h (v : V) w = 0 := v.2
      simp only [HermSp.perpEquiv_apply, HermSp.perpForm_h]
      rw [B.norm_perp hv a]
      constructor
      · intro h; rw [h]; ring
      · intro h; rw [← h]; ring)
  exact e1.symm.trans
    ⟨fun x => ⟨x.1.1, x.1.2, x.2⟩, fun s => ⟨(s.1, s.2.1), s.2.2⟩, fun _ => rfl, fun _ => rfl⟩

theorem sum_ite_card {E : Type} [Fintype E] (p : E → Prop) (A B₀ : ℝ) [DecidablePred p] :
    ∑ a, (if p a then B₀ else A) =
      (Nat.card {a // p a} : ℝ) * B₀ + ((Nat.card E : ℝ) - Nat.card {a // p a}) * A := by
  have h : ∀ a, (if p a then B₀ else A) = A + (B₀ - A) * (if p a then 1 else 0) := by
    intro a; split_ifs <;> ring
  simp only [h]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_const,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [Finset.card_univ, nsmul_eq_mul]
  ring

theorem arith_unit (q ε x Q : ℝ) (hq : q ≠ 0) :
    (q - ε) * (Q / q * (1 + (q - 1) * x)) + (q ^ 2 - (q - ε)) * (Q / q * (1 - x)) =
      Q * q ^ 2 / q * (1 - x * (ε / q)) := by
  field_simp
  ring

theorem arith_zero (q ε x Q : ℝ) (hq : q ≠ 0) :
    (q * (1 + ε) - ε) * (Q / q * (1 + (q - 1) * x)) +
        (q ^ 2 - (q * (1 + ε) - ε)) * (Q / q * (1 - x)) =
      Q * q ^ 2 / q * (1 + (q - 1) * (x * (ε / q))) := by
  field_simp
  ring

theorem count : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V), Nat.card V = q ^ (2 * m) → (∀ c : E, τ c = c → c ≠ 0 → (Nat.card {v : V // B.h v v = c} : ℝ) = (q : ℝ) ^ (2 * m) / q * (1 - ((ε : ℝ) / q) ^ m)) ∧ (Nat.card {v : V // B.h v v = 0} : ℝ) = (q : ℝ) ^ (2 * m) / q * (1 + ((q : ℝ) - 1) * ((ε : ℝ) / q) ^ m) := by
  intro E _ τ q ε hR m
  have hq1 : 1 < q := hR.one_lt
  have hq0 : (q : ℝ) ≠ 0 := by
    have : 0 < q := by omega
    exact_mod_cast this.ne'
  induction m with
  | zero =>
    intro V _ _ B hc
    have hc1 : Nat.card V = 1 := by simpa using hc
    obtain ⟨hs, -⟩ := Nat.card_eq_one_iff_unique.1 hc1
    refine ⟨?_, ?_⟩
    · intro c _ hc0
      have : IsEmpty {v : V // B.h v v = c} :=
        ⟨fun x => hc0 (by
          have h := x.2
          rw [Subsingleton.elim x.1 0, B.zero_left] at h
          exact h.symm)⟩
      rw [Nat.card_of_isEmpty]
      simp
    · have : Subsingleton {v : V // B.h v v = 0} := inferInstance
      rw [Nat.card_of_subsingleton (⟨0, B.zero_left 0⟩ : {v : V // B.h v v = 0})]
      field_simp
      ring
  | succ m ih =>
    intro V _ _ B hc
    have hpow : 1 < q ^ (2 * (m + 1)) := Nat.one_lt_pow (by omega) hq1
    have hfin : Finite V := Nat.finite_of_card_ne_zero (by omega)
    have hfinE : Finite E := Nat.finite_of_card_ne_zero (by
      rw [hR.card]; exact pow_ne_zero _ (by omega))
    have hnt : Nontrivial V := Finite.one_lt_card_iff_nontrivial.1 (by omega)
    obtain ⟨w, hw⟩ := GlobalTheory.T.hermitian_space_anisotropic_unit E τ q ε hR V B hnt
    have hP : Nat.card (B.perp w) = q ^ (2 * m) := by
      have h1 : Nat.card E * Nat.card (B.perp w) = Nat.card V := by
        rw [← Nat.card_prod]; exact Nat.card_congr (B.perpEquiv hw)
      rw [hR.card, hc] at h1
      have hq2 : 0 < q ^ 2 := pow_pos (by omega) _
      apply Nat.eq_of_mul_eq_mul_left hq2
      rw [h1]; ring
    obtain ⟨ihc, ihz⟩ := ih (B.perp w) (B.perpForm hw) hP
    classical
    haveI := Fintype.ofFinite E
    have hdfix : τ (B.h w w) = B.h w w := (B.symm w w).symm
    obtain ⟨di, hdi⟩ : ∃ di, B.h w w * di = 1 := hw.exists_right_inv
    have hdifix : τ di = di := by
      have h1 : B.h w w * τ di = 1 := by
        have := congrArg τ hdi
        rwa [map_mul, hdfix, map_one] at this
      calc τ di = (B.h w w * di) * τ di := by rw [hdi, one_mul]
        _ = di * (B.h w w * τ di) := by ring
        _ = di := by rw [h1, mul_one]
    set A : ℝ := (q : ℝ) ^ (2 * m) / q * (1 - ((ε : ℝ) / q) ^ m) with hA
    set B₀ : ℝ := (q : ℝ) ^ (2 * m) / q * (1 + ((q : ℝ) - 1) * ((ε : ℝ) / q) ^ m) with hB₀
    have key : ∀ c : E, τ c = c → (Nat.card {v : V // B.h v v = c} : ℝ) =
        (Nat.card {a : E // a * τ a = c * di} : ℝ) * B₀ +
          ((q : ℝ) ^ 2 - Nat.card {a : E // a * τ a = c * di}) * A := by
      intro c hcf
      have hiff : ∀ a : E, a * τ a * B.h w w = c ↔ a * τ a = c * di := by
        intro a
        constructor
        · intro h
          rw [← h, mul_assoc, hdi, mul_one]
        · intro h
          rw [h, mul_assoc, mul_comm di, hdi, mul_one]
      have hterm : ∀ a : E,
          (Nat.card {v : B.perp w // (B.perpForm hw).h v v = c - a * τ a * B.h w w} : ℝ) =
            if a * τ a = c * di then B₀ else A := by
        intro a
        split_ifs with h
        · have h0 : c - a * τ a * B.h w w = 0 := by rw [(hiff a).2 h, sub_self]
          rw [h0]; exact ihz
        · refine ihc _ ?_ ?_
          · rw [map_sub, map_mul, map_mul, hcf, hdfix, hR.inv a]
            ring
          · intro h0
            exact h ((hiff a).1 (sub_eq_zero.1 h0).symm)
      rw [card_fibre B hw c]
      push_cast
      rw [Finset.sum_congr rfl (fun a _ => hterm a), sum_ite_card, hR.card]
      push_cast
      rfl
    have hpw : (q : ℝ) ^ (2 * (m + 1)) = (q : ℝ) ^ (2 * m) * (q : ℝ) ^ 2 := by ring
    refine ⟨?_, ?_⟩
    · intro c hcf hc0
      have hn : (Nat.card {a : E // a * τ a = c * di} : ℝ) = (q : ℝ) - ε := by
        have := GlobalTheory.T.norm_fibre_card_nonzero E τ q ε hR (c * di)
          (by rw [map_mul, hcf, hdifix])
          (by
            intro h0
            apply hc0
            calc c = c * (di * B.h w w) := by rw [mul_comm di, hdi, mul_one]
              _ = (c * di) * B.h w w := by ring
              _ = 0 := by rw [h0, zero_mul])
        exact_mod_cast this
      rw [key c hcf, hn, hpw, pow_succ ((ε : ℝ) / q) m]
      exact arith_unit _ _ _ _ hq0
    · have hn : (Nat.card {a : E // a * τ a = (0 : E) * di} : ℝ) = (q : ℝ) * (1 + ε) - ε := by
        have := GlobalTheory.T.norm_fibre_card_zero E τ q ε hR
        rw [zero_mul]
        exact_mod_cast this
      rw [key 0 (map_zero τ), hn, hpw, pow_succ ((ε : ℝ) / q) m]
      exact arith_zero _ _ _ _ hq0

end GlobalTheory.CompanionTheory.UnrDens.Sphere
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InverseTransformRecoversFunction
section
noncomputable section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier.PhiInv

theorem dot_pt_eq (x y t : ℝ × ℝ) :
    dot (pt x y) t = ((rdot x t : ℝ) : ℂ) + Complex.I * ((rdot y t : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [dot, pt, rdot]

theorem integrable_gaussian_prod :
    Integrable (fun y : ℝ × ℝ => Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) := by
  have h1 : Integrable (fun x : ℝ => Real.exp (-1 * x ^ 2)) := integrable_exp_neg_mul_sq one_pos
  have h2 := h1.mul_prod h1
  rw [← Measure.volume_eq_prod] at h2
  refine h2.congr (Eventually.of_forall fun y => ?_)
  simp only
  rw [← Real.exp_add]
  congr 1
  ring

theorem phi_eq_smul {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (G : ℂ × ℂ → X) (x t : ℝ × ℝ) :
    phi G x t = Complex.exp (-((rdot x t : ℝ) : ℂ)) •
      ∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y t : ℝ) : ℂ))) • G (pt x y) := by
  unfold phi
  rw [← integral_smul]
  congr 1
  funext y
  rw [smul_smul, dot_pt_eq, ← Complex.exp_add]
  congr 2
  ring

theorem hat_eq_smul {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (G : ℂ × ℂ → X) (x t : ℝ × ℝ) :
    (∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y t : ℝ) : ℂ))) • G (pt x y)) =
      Complex.exp ((rdot x t : ℝ) : ℂ) • phi G x t := by
  rw [phi_eq_smul, smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]

theorem inv_phi_eq : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (G : ℂ × ℂ → X)
    (x : ℝ × ℝ), Continuous (fun y => G (pt x y)) →
    (∃ M : ℝ, ∀ y : ℝ × ℝ, ‖G (pt x y)‖ ≤ M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) →
    Continuous (phi G x) →
    (∃ ε : ℝ, 0 < ε ∧ ∃ M : ℝ, ∀ t : ℝ × ℝ,
      ‖phi G x t‖ ≤ M * Real.exp (-rdot x t) * Real.exp (-ε * (|t.1| + |t.2|))) →
    ∀ y : ℝ × ℝ, inv (phi G x) (pt x y) = G (pt x y) := by
  intro X _ _ _ G x hc ⟨M, hM⟩ hphic ⟨ε, hε, M', hM'⟩ y
  have hint : Integrable (fun y : ℝ × ℝ => G (pt x y)) :=
    Integrable.mono' (integrable_gaussian_prod.const_mul M) hc.aestronglyMeasurable
      (Eventually.of_forall fun y => hM y)
  have hdx : ∀ t, dot (pt x 0) t = ((rdot x t : ℝ) : ℂ) := by
    intro t; rw [dot_pt_eq]; simp [rdot]
  have hl : ((pt x 0).1.re, (pt x 0).2.re) = x := by simp [pt]
  have hint2 : Integrable (fun t : ℝ × ℝ =>
      ∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y t : ℝ) : ℂ))) • G (pt x y)) := by
    have h0 := (GlobalTheory.T.exponential_fourier_integral_bound X (phi G x) (pt x 0) ε M' hε hphic (by rw [hl]; exact hM')).1
    refine h0.congr (Eventually.of_forall fun t => ?_)
    show Complex.exp (dot (pt x 0) t) • phi G x t =
      ∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y t : ℝ) : ℂ))) • G (pt x y)
    rw [hdx, hat_eq_smul]
  have key := GlobalTheory.T.fourier_inversion_real_plane X (fun y => G (pt x y)) hc hint hint2 y
  rw [key]
  unfold inv
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  beta_reduce
  rw [hat_eq_smul, smul_smul, dot_pt_eq, ← Complex.exp_add]
  congr 2
  ring

end GlobalTheory.CompanionTheory.TubeFourier.PhiInv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewtonApproximationLocalToGlobalStatement
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newton_approximation_local_to_global : ∀ {S : Type} [CommRing S] (ϖ : S), (∀ m : Ideal S, m.IsMaximal → Step (Ideal.Quotient.mk (compI m) ϖ)) → Step ϖ := by
  first | exact @GlobalTheory.CompanionTheory.NewtonStep.step_of_forall_maximal | exact GlobalTheory.CompanionTheory.NewtonStep.step_of_forall_maximal | (intros; apply GlobalTheory.CompanionTheory.NewtonStep.step_of_forall_maximal <;> assumption)
end

