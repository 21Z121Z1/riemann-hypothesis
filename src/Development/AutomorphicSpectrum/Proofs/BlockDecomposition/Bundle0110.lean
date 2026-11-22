import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0100
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0091
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0049
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0104
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0101
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactnessStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0038
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCongruenceRefinement

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdditiveCharacterSumOrthogonality
section
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

namespace GlobalTheory.CompanionTheory.TyFin.Orth

theorem sum_inv_addChar_mul_left (K : Type) [Field K] [Fintype K] [DecidableEq K]
    (ψ₀ : AddChar K ℂ) (hψ : ψ₀ ≠ 1) (x : K) :
    (∑ t : K, (ψ₀ (t * x))⁻¹) = if x = 0 then (Fintype.card K : ℂ) else 0 := by
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [if_neg hx]
    have hbij : Function.Bijective (fun t : K => -(t * x)) := by
      refine ⟨fun a b h => ?_, fun b => ⟨-(b * x⁻¹), ?_⟩⟩
      · exact mul_right_cancel₀ hx (neg_injective h)
      · simp [hx]
    have h1 : (∑ t : K, (ψ₀ (t * x))⁻¹) = ∑ t : K, ψ₀ (-(t * x)) :=
      Finset.sum_congr rfl fun t _ => (AddChar.map_neg_eq_inv ψ₀ (t * x)).symm
    rw [h1, hbij.sum_comp (fun u => ψ₀ u)]
    exact AddChar.sum_eq_zero_of_ne_one hψ

theorem sum_inv_addChar_dot (K : Type) [Field K] [Fintype K] [DecidableEq K] (j : ℕ)
    (ψ₀ : AddChar K ℂ) (hψ : ψ₀ ≠ 1) (x : Fin j → K) :
    (∑ r : Fin j → K, (ψ₀ (∑ i, r i * x i))⁻¹)
      = if x = 0 then (Fintype.card K : ℂ) ^ j else 0 := by
  have h1 : ∀ r : Fin j → K, (ψ₀ (∑ i, r i * x i))⁻¹ = ∏ i, (ψ₀ (r i * x i))⁻¹ := by
    intro r
    have hs : ∀ s : Finset (Fin j), ψ₀ (∑ i ∈ s, r i * x i) = ∏ i ∈ s, ψ₀ (r i * x i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
    rw [hs, Finset.prod_inv_distrib]
  have h2 : (∑ r : Fin j → K, ∏ i, (ψ₀ (r i * x i))⁻¹)
      = ∏ i, ∑ t : K, (ψ₀ (t * x i))⁻¹ := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp_rw [h1]
  rw [h2]
  simp_rw [sum_inv_addChar_mul_left K ψ₀ hψ]
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [if_neg hx]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem orth : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (j : ℕ) (ψ₀ : AddChar K ℂ),
    ψ₀ ≠ 1 → ∀ x : Fin j → K,
    (∑ r : Fin j → K, (ψ₀ (∑ i, r i * x i))⁻¹) = if x = 0 then (Fintype.card K : ℂ) ^ j else 0 :=
  fun K _ _ _ j ψ₀ hψ x => sum_inv_addChar_dot K j ψ₀ hψ x

end GlobalTheory.CompanionTheory.TyFin.Orth
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanFundamentalDomainIntegersStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_fundamental_domain_integers : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ li : Measure (Ainf F), IsStdInf li → ∃ D K₀ : Set (Ainf F), MeasurableSet D ∧ IsCompact K₀ ∧ D ⊆ K₀ ∧ li D = 1 ∧ ∀ y : Ainf F, ∃! a : 𝓞 F, y - algebraMap F (Ainf F) (a : F) ∈ D := by
  first | exact @GlobalTheory.CompanionTheory.Equi.exists_bounded_infDomain | exact GlobalTheory.CompanionTheory.Equi.exists_bounded_infDomain | (intros; apply GlobalTheory.CompanionTheory.Equi.exists_bounded_infDomain <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockEmbeddingGLInverse
section
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL

variable (K : Type) [Field K]

theorem sum_fin_of_ge_zero {d j : ℕ} (hjd : j ≤ d) (f : Fin d → K)
    (hf : ∀ k : Fin d, j ≤ (k : ℕ) → f k = 0) :
    ∑ k, f k = ∑ k : Fin j, f (Fin.castLE hjd k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjd
  rw [Fin.sum_univ_add]
  have h0 : ∑ k : Fin m, f (Fin.natAdd j k) = 0 :=
    Finset.sum_eq_zero fun k _ => hf _ (by simp)
  rw [h0, add_zero]
  rfl

theorem blkEmb_row_ge {d j : ℕ} (A : Matrix (Fin j) (Fin j) K) (i l : Fin d)
    (hi : j ≤ (i : ℕ)) : blkEmb K d j A i l = if i = l then 1 else 0 := by
  simp only [GlobalTheory.CompanionTheory.TyFin.ColStep.blkEmb]
  rw [dif_neg fun h => (not_lt.2 hi) h.1]

theorem blkEmb_col_ge {d j : ℕ} (A : Matrix (Fin j) (Fin j) K) (i l : Fin d)
    (hl : j ≤ (l : ℕ)) : blkEmb K d j A i l = if i = l then 1 else 0 := by
  simp only [GlobalTheory.CompanionTheory.TyFin.ColStep.blkEmb]
  rw [dif_neg fun h => (not_lt.2 hl) h.2]

theorem blkEmb_lt {d j : ℕ} (A : Matrix (Fin j) (Fin j) K) (i l : Fin d)
    (hi : (i : ℕ) < j) (hl : (l : ℕ) < j) :
    blkEmb K d j A i l = A ⟨i, hi⟩ ⟨l, hl⟩ := by
  simp only [GlobalTheory.CompanionTheory.TyFin.ColStep.blkEmb]
  rw [dif_pos ⟨hi, hl⟩]

theorem blkEmb_one (d j : ℕ) : blkEmb K d j (1 : Matrix (Fin j) (Fin j) K) = 1 := by
  ext i l
  rw [Matrix.one_apply]
  by_cases hi : (i : ℕ) < j
  · by_cases hl : (l : ℕ) < j
    · rw [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_lt K _ i l hi hl, Matrix.one_apply]
      simp [Fin.ext_iff]
    · exact GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_col_ge K _ i l (not_lt.1 hl)
  · exact GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_row_ge K _ i l (not_lt.1 hi)

theorem blkEmb_mul {d j : ℕ} (hjd : j ≤ d) (A B : Matrix (Fin j) (Fin j) K) :
    blkEmb K d j (A * B) = blkEmb K d j A * blkEmb K d j B := by
  ext i l
  rw [Matrix.mul_apply]
  by_cases hi : (i : ℕ) < j
  · by_cases hl : (l : ℕ) < j
    · rw [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_lt K _ i l hi hl, Matrix.mul_apply,
        GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.sum_fin_of_ge_zero K hjd]
      · refine Finset.sum_congr rfl fun k _ => ?_
        have hk : ((Fin.castLE hjd k : Fin d) : ℕ) < j := k.2
        rw [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_lt K _ i _ hi hk,
          GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_lt K _ _ l hk hl]
        rfl
      · intro k hk
        rw [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_col_ge K _ i k hk, if_neg (by rintro rfl; omega),
          zero_mul]
    · have hl' : j ≤ (l : ℕ) := not_lt.1 hl
      rw [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_col_ge K _ i l hl']
      simp only [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_col_ge K B _ l hl', mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true,
        GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_col_ge K A i l hl']
  · have hi' : j ≤ (i : ℕ) := not_lt.1 hi
    rw [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_row_ge K _ i l hi']
    simp only [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_row_ge K A i _ hi', ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_row_ge K B i l hi']

theorem exists_gl_blkEmb : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ), j ≤ d →
    ∀ g : GL (Fin j) K, ∃ h : GL (Fin d) K,
    (h : Matrix (Fin d) (Fin d) K) = blkEmb K d j (g : Matrix (Fin j) (Fin j) K) ∧
    ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K) := by
  intro K _ _ _ d j hjd g
  refine ⟨⟨GlobalTheory.CompanionTheory.TyFin.ColStep.blkEmb K d j (g : Matrix (Fin j) (Fin j) K),
    GlobalTheory.CompanionTheory.TyFin.ColStep.blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K), ?_, ?_⟩, rfl, rfl⟩
  · rw [← GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_mul K hjd, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_one]
  · rw [← GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_mul K hjd, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_one]

end GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedCokernelLimitToLevelStatement
section
open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_cokernel_limit_to_level : ∀ (W : Type) [CommRing W] [IsNoetherianRing W] (l : ℕ) (S S' : Sys.{1} W) (_ : LSeq l S S'), (∀ n, IsArtinian W (S.M n)) → Module.Finite W S'.lim → ∃ c : ℕ, ∀ n (x : S.M n), ∃ y : S.lim, y.1 n = ((l : W) ^ c) • x := by
  first | exact @GlobalTheory.CompanionTheory.TwCok.lim_cokernel_bounded | exact GlobalTheory.CompanionTheory.TwCok.lim_cokernel_bounded | (intros; apply GlobalTheory.CompanionTheory.TwCok.lim_cokernel_bounded <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatDecompositionTwoBlocksStatement
section
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bruhat_decomposition_two_blocks : ReciprocityTheory.Ty.Fin.St.BruhatTwo := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.Bruhat.bruhatTwo | exact GlobalTheory.CompanionTheory.TyFin.Bruhat.bruhatTwo | (intros; apply GlobalTheory.CompanionTheory.TyFin.Bruhat.bruhatTwo <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatDecompositionUniqueStatement
section
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bruhat_decomposition_unique : ReciprocityTheory.Ty.Fin.St.BruhatUniq := by
  first | exact @GlobalTheory.CompanionTheory.BruhatInv.bruhatUniq | exact GlobalTheory.CompanionTheory.BruhatInv.bruhatUniq | (intros; apply GlobalTheory.CompanionTheory.BruhatInv.bruhatUniq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardOrthonormalFramesHermitianSpace
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens.OrthCount

variable {E : Type} [CommRing E] {τ : E →+* E} {V : Type} [AddCommGroup V] [Module E V]

abbrev Tuples (B : HermSp E τ V) (n : ℕ) : Type :=
  {x : Fin n → V // ∀ i j, B.h (x i) (x j) = if i = j then 1 else 0}

theorem isUnit_norm (B : HermSp E τ V) (w : {w : V // B.h w w = 1}) : IsUnit (B.h w.1 w.1) := by
  rw [w.2]; exact isUnit_one

noncomputable def consEquiv (B : HermSp E τ V) (n : ℕ) :
    Tuples B (n + 1) ≃
      Σ w : {w : V // B.h w w = 1}, Tuples (B.perpForm (isUnit_norm B w)) n where
  toFun x := ⟨⟨x.1 0, by simpa using x.2 0 0⟩,
    ⟨fun j => ⟨x.1 j.succ, by
      show B.h (x.1 j.succ) (x.1 0) = 0
      simpa [Fin.succ_ne_zero] using x.2 j.succ 0⟩, fun i j => by
      simpa using x.2 i.succ j.succ⟩⟩
  invFun p := ⟨Fin.cons p.1.1 (fun j => (p.2.1 j : V)), by
    obtain ⟨⟨w, hw⟩, ⟨y, hy⟩⟩ := p
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hw
    · have h0 : B.h (y j : V) w = 0 := (y j).2
      simp [B.symm (y j : V) w, h0, (Fin.succ_ne_zero j).symm]
    · have h0 : B.h (y i : V) w = 0 := (y i).2
      simp [h0, Fin.succ_ne_zero i]
    · simpa using hy i j⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    refine Fin.cases rfl (fun j => rfl) i
  right_inv p := by
    obtain ⟨⟨w, hw⟩, ⟨y, hy⟩⟩ := p
    rfl

end GlobalTheory.CompanionTheory.UnrDens.OrthCount

namespace GlobalTheory.CompanionTheory.UnrDens

open OrthCount in

theorem card_orthonormal_tuples : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (n m : ℕ), n ≤ m → ∀ (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V), Nat.card V = q ^ (2 * m) → (Nat.card {x : Fin n → V // ∀ i j, B.h (x i) (x j) = if i = j then 1 else 0} : ℝ) = ∏ i : Fin n, ((q : ℝ) ^ (2 * (m - (i : ℕ))) / q * (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ)))) := by
  intro E _ τ q ε hR n
  induction n with
  | zero =>
    intro m _ V _ _ B _
    have h1 : Nat.card {x : Fin 0 → V // ∀ i j, B.h (x i) (x j) = if i = j then 1 else 0} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => Subtype.ext (funext fun i => i.elim0)⟩,
        ⟨⟨fun i => i.elim0, fun i => i.elim0⟩⟩⟩
    simp [h1]
  | succ n ih =>
    intro m hnm V _ _ B hc
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hq : 1 < q := hR.one_lt
    have hq0 : q ≠ 0 := by omega
    haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hq0)
    haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hR.card]; exact pow_ne_zero _ hq0)
    haveI : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 (by rw [hR.card]; nlinarith)
    have hsph := (GlobalTheory.T.hermitian_vector_values_card E τ q ε hR (m' + 1) V B hc).1 1 (map_one τ) one_ne_zero
    have hperp : ∀ w : {w : V // B.h w w = 1}, Nat.card (B.perp w.1) = q ^ (2 * m') := by
      intro w
      have h1 := Nat.card_congr (B.perpEquiv (isUnit_norm B w))
      rw [Nat.card_prod, hR.card, hc] at h1
      have h2 : q ^ (2 * (m' + 1)) = q ^ 2 * q ^ (2 * m') := by ring
      rw [h2] at h1
      exact Nat.eq_of_mul_eq_mul_left (pow_pos (by omega) 2) h1
    have hfib : ∀ w : {w : V // B.h w w = 1},
        (Nat.card (Tuples (B.perpForm (isUnit_norm B w)) n) : ℝ) =
          ∏ i : Fin n, ((q : ℝ) ^ (2 * (m' - (i : ℕ))) / q * (1 - ((ε : ℝ) / q) ^ (m' - (i : ℕ)))) :=
      fun w => ih m' (by omega) (B.perp w.1) (B.perpForm (isUnit_norm B w)) (hperp w)
    haveI : Fintype {w : V // B.h w w = 1} := Fintype.ofFinite _
    have hcard : (Nat.card (Tuples B (n + 1)) : ℝ) =
        (Nat.card {w : V // B.h w w = 1} : ℝ) *
          ∏ i : Fin n, ((q : ℝ) ^ (2 * (m' - (i : ℕ))) / q * (1 - ((ε : ℝ) / q) ^ (m' - (i : ℕ)))) := by
      rw [Nat.card_congr (consEquiv B n), Nat.card_sigma]
      push_cast
      rw [Finset.sum_congr rfl (fun w _ => hfib w), Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Nat.card_eq_fintype_card]
    change (Nat.card (Tuples B (n + 1)) : ℝ) = _
    rw [hcard, hsph, Fin.prod_univ_succ]
    simp [Nat.add_sub_add_right]

end GlobalTheory.CompanionTheory.UnrDens
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardParabolicSubgroupStatement
section
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_parabolic_subgroup : ReciprocityTheory.Ty.Fin.St.CardParab := by
  first | exact @GlobalTheory.CompanionTheory.FinGL.cardParab | exact GlobalTheory.CompanionTheory.FinGL.cardParab | (intros; apply GlobalTheory.CompanionTheory.FinGL.cardParab <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CmpPutSucc
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
open GlobalTheory.CatH (face toLast)
universe w w' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.ReesDown

section
variable {R : Type} [CommRing R] {D : Type u} [Category.{v} D] {F : D ⥤ ModuleCat.{w} R} (Ψ : Flt F)

def ev (r : ℕ) (T : D) : Ψ.Pr T →+ F.obj T where
  toFun x := (x r).1
  map_zero' := rfl
  map_add' _ _ := rfl

def cmp (r j : ℕ) (f : Cn Ψ.rees j) : Cn F j := fun s => ev Ψ r _ (f s)

def cmpS (r j : ℕ) (f : Cn Ψ.rees j) : Cn (Ψ.S r).fn j := fun s => (show Ψ.Pr _ from f s) r

def put (h0 : ∀ T, (Ψ.S 0).S T = ⊤) (j : ℕ) (z : Cn F j) : Cn Ψ.rees j := fun s =>
  show Ψ.Pr _ from fun r => match r with
    | 0 => ⟨z s, by rw [h0]; trivial⟩
    | _ + 1 => 0

theorem cmp_d (r j : ℕ) (f : Cn Ψ.rees j) : cmp Ψ r (j + 1) (d Ψ.rees j f) = d F j (cmp Ψ r j f) := by
  funext s
  refine (map_sum (ev Ψ r _) _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [map_zsmul]
  rfl

theorem cmp_zero (r j : ℕ) : cmp Ψ r j 0 = 0 := rfl

theorem cmp_sub (r j : ℕ) (f g : Cn Ψ.rees j) : cmp Ψ r j (f - g) = cmp Ψ r j f - cmp Ψ r j g := rfl

theorem cmp_put_zero (h0 : ∀ T, (Ψ.S 0).S T = ⊤) (j : ℕ) (z : Cn F j) : cmp Ψ 0 j (put Ψ h0 j z) = z := rfl

theorem cmp_put_succ (h0 : ∀ T, (Ψ.S 0).S T = ⊤) (r j : ℕ) (z : Cn F j) : cmp Ψ (r + 1) j (put Ψ h0 j z) = 0 := rfl

theorem cochain_ext {j : ℕ} {f g : Cn Ψ.rees j} (h : ∀ r, cmp Ψ r j f = cmp Ψ r j g) : f = g := by
  funext s
  refine funext fun r => Subtype.ext ?_
  exact congrFun (h r) s

theorem put_d (h0 : ∀ T, (Ψ.S 0).S T = ⊤) (j : ℕ) (z : Cn F j) :
    d Ψ.rees j (put Ψ h0 j z) = put Ψ h0 (j + 1) (d F j z) := by
  refine cochain_ext Ψ fun r => ?_
  rw [cmp_d]
  cases r with
  | zero => rfl
  | succ r =>
    rw [cmp_put_succ, cmp_put_succ, map_zero]

theorem put_zero (h0 : ∀ T, (Ψ.S 0).S T = ⊤) (j : ℕ) : put Ψ h0 j 0 = 0 := by
  refine cochain_ext Ψ fun r => ?_
  cases r <;> rfl

theorem cmp_X (j r : ℕ) (f : Cn Ψ.rees j) : cmp Ψ (r + 1) j ((X : ℤ[X]) • f) = Ψ.μ • cmp Ψ r j f := by
  funext s
  exact Ψ.X_smul_succ _ (f s) r

theorem cmp_X_pow (j k : ℕ) (f : Cn Ψ.rees j) : cmp Ψ k j ((X : ℤ[X]) ^ k • f) = Ψ.μ ^ k • cmp Ψ 0 j f := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_smul, cmp_X, ih, pow_succ', mul_smul]

theorem cmp_mem_B (r j : ℕ) (a : Cn Ψ.rees j) (h : a ∈ (cx Ψ.rees).B j) : cmp Ψ r j a ∈ (cx F).B j := by
  cases j with
  | zero =>
    have : a = 0 := h
    rw [this]
    exact Submodule.zero_mem _
  | succ j =>
    obtain ⟨e, rfl⟩ := h
    exact ⟨cmp Ψ r j e, (cmp_d Ψ r j e).symm⟩

theorem put_mem_B (h0 : ∀ T, (Ψ.S 0).S T = ⊤) (j : ℕ) (a : Cn F j) (h : a ∈ (cx F).B j) :
    put Ψ h0 j a ∈ (cx Ψ.rees).B j := by
  cases j with
  | zero =>
    have : a = 0 := h
    rw [this, put_zero]
    exact Submodule.zero_mem _
  | succ j =>
    obtain ⟨e, rfl⟩ := h
    exact ⟨put Ψ h0 j e, put_d Ψ h0 j e⟩

theorem d_cmpS (r j : ℕ) (f : Cn Ψ.rees j) (hf : d Ψ.rees j f = 0) : d (Ψ.S r).fn j (cmpS Ψ r j f) = 0 := by
  funext s
  refine Subtype.ext ?_
  have h1 := congrFun ((Ψ.S r).inc.d_pullC j (cmpS Ψ r j f)) s
  have h2 : d F j (cmp Ψ r j f) = 0 := by rw [← cmp_d, hf, cmp_zero]
  exact h1.symm.trans (congrFun h2 s)

end

end GlobalTheory.CompanionTheory.ReesDown

namespace GlobalTheory.CompanionTheory.ReesDown

theorem put_pull {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {F : C ⥤ ModuleCat.{w} R} (Φ : Flt F) (G : C' ⥤ C) (h0 : ∀ T, (Φ.S 0).S T = ⊤) (j : ℕ) (z : Cn F j) :
    (Mor.restrict Φ.rees G).pullC j (put Φ h0 j z) =
      put (Φ.comap G) (fun T => h0 (G.obj T)) j ((Mor.restrict F G).pullC j z) := by
  refine cochain_ext (Φ.comap G) fun r => ?_
  cases r <;> rfl

theorem main : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {F : C ⥤ ModuleCat.{w} R} (Φ : Flt F) (G : C' ⥤ C) (n N : ℕ), (∀ T, (Φ.S 0).S T = ⊤) → RI ((X : ℤ[X]) ^ N) n Φ.rees G → ∀ j ≤ n, InjUpTo (Φ.μ ^ N) ((Mor.restrict F G).pull j) ∧ ∀ y, ∃ x ∈ (Φ.S N).img j, (Mor.restrict F G).pull j x = Φ.μ ^ N • y := by
  intro R _ C _ C' _ F Φ G n N h0 hRI j hj
  have hU : UpTo ((X : ℤ[X]) ^ N) ((Mor.restrict Φ.rees G).pull j) := hRI j hj
  have h0' : ∀ T, ((Φ.comap G).S 0).S T = ⊤ := fun T => h0 (G.obj T)
  have hpd : ∀ (z : Cn F j), d F j z = 0 → d (G ⋙ F) j ((Mor.restrict F G).pullC j z) = 0 := fun z hz => by
    rw [Mor.d_pullC, hz, map_zero]
  refine ⟨fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨z, hz, rfl⟩ := (P.cls_surj (cx F) j).1 x
    have h2 : (Mor.restrict F G).pullC j z ∈ (cx (G ⋙ F)).B j := by
      have h1 := P.mapH_cls (Mor.restrict F G).hom j z hz (hpd z hz)
      exact ((P.cls_surj (cx (G ⋙ F)) j).2.1 _ _).1 (h1.symm.trans hx)
    have hZ : d Φ.rees j (put Φ h0 j z) = 0 := by
      rw [put_d, hz]; exact put_zero Φ h0 _
    have hZ' : d (G ⋙ Φ.rees) j ((Mor.restrict Φ.rees G).pullC j (put Φ h0 j z)) = 0 := by
      rw [Mor.d_pullC, hZ, map_zero]
    have h3 : (Mor.restrict Φ.rees G).pull j ((cx Φ.rees).cls _ hZ) = 0 := by
      refine (P.mapH_cls (Mor.restrict Φ.rees G).hom j _ hZ hZ').trans ?_
      refine ((P.cls_surj (cx (G ⋙ Φ.rees)) j).2.1 _ _).2 ?_
      have key : ∀ a : (cx (G ⋙ Φ.rees)).X j, a = put (Φ.comap G) h0' j ((Mor.restrict F G).pullC j z) →
          a ∈ (cx (G ⋙ Φ.rees)).B j := by
        intro a ha
        subst ha
        exact put_mem_B (Φ.comap G) h0' j _ h2
      exact key _ (put_pull Φ G h0 j z)
    have hXZ : d Φ.rees j ((X : ℤ[X]) ^ N • put Φ h0 j z) = 0 := by
      rw [map_smul, hZ, smul_zero]
    have h4 := hU.1 _ h3
    rw [← (P.cls_surj (cx Φ.rees) j).2.2.2.2 _ _ hZ hXZ] at h4
    have h5 := cmp_mem_B Φ N j _ (((P.cls_surj (cx Φ.rees) j).2.1 _ hXZ).1 h4)
    rw [cmp_X_pow, cmp_put_zero] at h5
    have hμ : d F j (Φ.μ ^ N • z) = 0 := by rw [map_smul, hz, smul_zero]
    rw [← (P.cls_surj (cx F) j).2.2.2.2 _ _ hz hμ]
    exact ((P.cls_surj (cx F) j).2.1 _ hμ).2 h5
  · obtain ⟨w, hw, rfl⟩ := (P.cls_surj (cx (G ⋙ F)) j).1 y
    have hW : d (G ⋙ Φ.rees) j (put (Φ.comap G) h0' j w) = 0 := by
      refine (put_d (Φ.comap G) h0' j w).trans ?_
      rw [hw]; exact put_zero (Φ.comap G) h0' _
    obtain ⟨x', hx'⟩ := hU.2 ((cx (G ⋙ Φ.rees)).cls (show (cx (G ⋙ Φ.rees)).X j from put (Φ.comap G) h0' j w) hW)
    obtain ⟨Z, hZ, rfl⟩ := (P.cls_surj (cx Φ.rees) j).1 x'
    have hZ' : d (G ⋙ Φ.rees) j ((Mor.restrict Φ.rees G).pullC j Z) = 0 := by
      rw [Mor.d_pullC, hZ, map_zero]
    have hXW : d (G ⋙ Φ.rees) j ((X : ℤ[X]) ^ N • put (Φ.comap G) h0' j w) = 0 := by
      rw [map_smul, hW, smul_zero]
    have hx2 := (P.mapH_cls (Mor.restrict Φ.rees G).hom j Z hZ hZ').symm.trans hx'
    rw [← (P.cls_surj (cx (G ⋙ Φ.rees)) j).2.2.2.2 _ _ hW hXW] at hx2
    have hB := ((P.cls_surj (cx (G ⋙ Φ.rees)) j).2.2.1 _ _ hZ' hXW).1 hx2
    have hc : (Mor.restrict F G).pullC j (cmp Φ N j Z) - Φ.μ ^ N • w ∈ (cx (G ⋙ F)).B j := by
      have h := cmp_mem_B (Φ.comap G) N j _ hB
      have e : ∀ A : Cn (Φ.comap G).rees j, A = (Mor.restrict Φ.rees G).pullC j Z →
          cmp (Φ.comap G) N j (A - (X : ℤ[X]) ^ N • put (Φ.comap G) h0' j w) =
            (Mor.restrict F G).pullC j (cmp Φ N j Z) - Φ.μ ^ N • w := by
        intro A hA
        rw [cmp_sub, cmp_X_pow, cmp_put_zero, hA]
        rfl
      exact (e _ rfl) ▸ h
    have hz0 : d F j (cmp Φ N j Z) = 0 := by rw [← cmp_d, hZ, cmp_zero]
    have hμ : d (G ⋙ F) j (Φ.μ ^ N • w) = 0 := by rw [map_smul, hw, smul_zero]
    refine ⟨(cx F).cls _ hz0, ⟨(cx (Φ.S N).fn).cls _ (d_cmpS Φ N j Z hZ), ?_⟩, ?_⟩
    · exact P.mapH_cls (Φ.S N).inc.hom j _ _ hz0
    · refine (P.mapH_cls (Mor.restrict F G).hom j _ hz0 (hpd _ hz0)).trans ?_
      rw [← (P.cls_surj (cx (G ⋙ F)) j).2.2.2.2 _ _ hw hμ]
      exact ((P.cls_surj (cx (G ⋙ F)) j).2.2.1 _ _ _ hμ).2 hc

end GlobalTheory.CompanionTheory.ReesDown
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactnessStatementStatement
section
open GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactness_statement : GlobalTheory.CompanionTheory.Jp.JpCmp := by
  first | exact @GlobalTheory.CompanionTheory.Jp.Cmp.jpCmp | exact GlobalTheory.CompanionTheory.Jp.Cmp.jpCmp | (intros; apply GlobalTheory.CompanionTheory.Jp.Cmp.jpCmp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCongruenceRefinementStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_congruence_refinement : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)), v ∉ S → ∀ (I : Ideal (𝓞 F)), I ≠ ⊥ → ¬ I ≤ v.asIdeal → ∀ (k : ℕ) (x0 : ι → F) (c : ι → Fv F v), ∃ x1 : ι → F, ∀ x : ι → F, (x ∈ cosetOff (insert v S) I x0 ∧ ∀ i, algebraMap F (Fv F v) (x i) - c i ∈ ballV v k) ↔ x ∈ cosetOff S (I * v.asIdeal ^ k) x1 := by
  first | exact @GlobalTheory.CompanionTheory.Equi.CosetStep.coset_step | exact GlobalTheory.CompanionTheory.Equi.CosetStep.coset_step | (intros; apply GlobalTheory.CompanionTheory.Equi.CosetStep.coset_step <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetEmptyPlacesLatticeStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_empty_places_lattice : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (I : Ideal (𝓞 F)) (x0 : ι → F), cosetOff (∅ : Finset (HeightOneSpectrum (𝓞 F))) I x0 = latCoset I x0 := by
  first | exact @GlobalTheory.CompanionTheory.Equi.cosetOff_empty_eq_latCoset | exact GlobalTheory.CompanionTheory.Equi.cosetOff_empty_eq_latCoset | (intros; apply GlobalTheory.CompanionTheory.Equi.cosetOff_empty_eq_latCoset <;> assumption)
end

