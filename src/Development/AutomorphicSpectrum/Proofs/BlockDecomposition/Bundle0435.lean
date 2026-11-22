import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.JPred
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0227
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0403
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0411
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0397
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0408
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0412

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialOfConjTorus
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.LbElem.ConjMonomial

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stdBlocks_ones (N : ℕ) (a : Fin N) (i : Fin (ones N a)) :
    stdBlocks (ones N) (sum_ones N) ⟨a, i⟩ = a := by
  apply Fin.ext
  rw [stdBlocks_val]
  have hi : (i : ℕ) = 0 := by
    have := i.2
    simp only [ones] at this
    omega
  simp [ones, hi]

theorem tor_offDiag {N : ℕ} {x : GL (Fin N) k} (hx : x ∈ Tor k N) {i j : Fin N} (hij : i ≠ j) :
    (x : Matrix (Fin N) (Fin N) k) i j = 0 := by
  obtain ⟨s, rfl⟩ := hx
  have h := leviEmb_apply_ne k (stdBlocks (ones N) (sum_ones N)) s hij
    (⟨0, by simp [ones]⟩ : Fin (ones N i)) (⟨0, by simp [ones]⟩ : Fin (ones N j))
  rwa [stdBlocks_ones, stdBlocks_ones] at h

theorem mem_tor_of_offDiag {N : ℕ} (x : GL (Fin N) k)
    (h : ∀ i j : Fin N, i ≠ j → (x : Matrix (Fin N) (Fin N) k) i j = 0) : x ∈ Tor k N := by
  have hd : ∀ i, (x : Matrix (Fin N) (Fin N) k) i i ≠ 0 := by
    intro i h0
    have h1 := congrArg (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i i) (mul_inv_cancel x)
    simp only [Units.val_mul, Units.val_one, Matrix.mul_apply, Matrix.one_apply_eq] at h1
    rw [Finset.sum_eq_zero] at h1
    · exact zero_ne_one h1
    · intro l _
      by_cases hl : i = l
      · subst hl
        rw [h0, zero_mul]
      · rw [h i l hl, zero_mul]
  refine ⟨fun a => Units.map (algebraMap k (Matrix (Fin (ones N a)) (Fin (ones N a)) k)).toMonoidHom
    (Units.mk0 _ (hd a)), ?_⟩
  apply Units.ext
  ext i j
  by_cases hij : i = j
  · subst hij
    have h1 := leviEmb_apply_same k (stdBlocks (ones N) (sum_ones N))
      (fun a => Units.map (algebraMap k (Matrix (Fin (ones N a)) (Fin (ones N a)) k)).toMonoidHom
        (Units.mk0 _ (hd a))) i (⟨0, by simp [ones]⟩ : Fin (ones N i)) (⟨0, by simp [ones]⟩ : Fin (ones N i))
    rw [stdBlocks_ones] at h1
    rw [h1]
    simp [Matrix.algebraMap_matrix_apply]
  · have h1 := leviEmb_apply_ne k (stdBlocks (ones N) (sum_ones N))
      (fun a => Units.map (algebraMap k (Matrix (Fin (ones N a)) (Fin (ones N a)) k)).toMonoidHom
        (Units.mk0 _ (hd a))) hij (⟨0, by simp [ones]⟩ : Fin (ones N i)) (⟨0, by simp [ones]⟩ : Fin (ones N j))
    rw [stdBlocks_ones, stdBlocks_ones] at h1
    rw [h i j hij]
    exact h1

theorem eq_diagonal_of_offDiag {N : ℕ} (M : Matrix (Fin N) (Fin N) k)
    (h : ∀ i j : Fin N, i ≠ j → M i j = 0) : M = Matrix.diagonal fun i => M i i := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · rw [h i j hij, Matrix.diagonal_apply_ne _ hij]

theorem monomial_of_conj_torus : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], ∀ (N : ℕ) (y D D' : GL (Fin N) k), D ∈ PositivityTheory.Lbc.Tor k N →
    D' ∈ PositivityTheory.Lbc.Tor k N →
    (∀ i j : Fin N, i ≠ j →
      (D' : Matrix (Fin N) (Fin N) k) i i ≠ (D' : Matrix (Fin N) (Fin N) k) j j) →
    y⁻¹ * D * y = D' →
    ∃ (σ : Equiv.Perm (Fin N)) (w : GL (Fin N) k), (w : Matrix (Fin N) (Fin N) k) = σ.permMatrix k ∧
      ∃ s ∈ PositivityTheory.Lbc.Tor k N, y = w * s := by
  intro k _ _ _ _ N y D D' hD hD' hdist hconj
  have hcomm : D * y = y * D' := by
    rw [← hconj]
    group
  have hmat : (D : Matrix (Fin N) (Fin N) k) * (y : Matrix (Fin N) (Fin N) k) =
      (y : Matrix (Fin N) (Fin N) k) * (D' : Matrix (Fin N) (Fin N) k) := by
    simpa using congrArg (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k)) hcomm
  have hent : ∀ i j, (D : Matrix (Fin N) (Fin N) k) i i * (y : Matrix (Fin N) (Fin N) k) i j =
      (y : Matrix (Fin N) (Fin N) k) i j * (D' : Matrix (Fin N) (Fin N) k) j j := by
    intro i j
    have h1 := congrFun (congrFun hmat i) j
    rw [eq_diagonal_of_offDiag (D : Matrix (Fin N) (Fin N) k) (fun a b hab => tor_offDiag hD hab),
      eq_diagonal_of_offDiag (D' : Matrix (Fin N) (Fin N) k) (fun a b hab => tor_offDiag hD' hab),
      Matrix.diagonal_mul, Matrix.mul_diagonal] at h1
    simpa using h1

  have hsupp : ∀ i j, (y : Matrix (Fin N) (Fin N) k) i j ≠ 0 →
      (D : Matrix (Fin N) (Fin N) k) i i = (D' : Matrix (Fin N) (Fin N) k) j j := by
    intro i j hij
    have h1 := hent i j
    rw [mul_comm] at h1
    exact mul_left_cancel₀ hij h1

  have hcol : ∀ j, ∃ i, (y : Matrix (Fin N) (Fin N) k) i j ≠ 0 := by
    intro j
    by_contra hc
    push_neg at hc
    have h1 := congrArg (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) j j) (inv_mul_cancel y)
    simp only [Units.val_mul, Units.val_one, Matrix.mul_apply, Matrix.one_apply_eq] at h1
    rw [Finset.sum_eq_zero (fun l _ => by rw [hc l, mul_zero])] at h1
    exact zero_ne_one h1
  choose f hf using hcol
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    apply hdist a b hne
    rw [← hsupp _ _ (hf a), ← hsupp _ _ (hf b), hab]
  have hbij : Function.Bijective f := Finite.injective_iff_bijective.1 hinj
  let τ : Equiv.Perm (Fin N) := Equiv.ofBijective f hbij
  have hτ : ∀ j, τ j = f j := fun j => rfl

  have hzero : ∀ i j, i ≠ f j → (y : Matrix (Fin N) (Fin N) k) i j = 0 := by
    intro i j hij
    by_contra hne
    obtain ⟨b, rfl⟩ := hbij.2 i
    have hbj : b ≠ j := fun e => hij (by rw [e])
    apply hdist b j hbj
    rw [← hsupp _ _ (hf b), ← hsupp _ _ hne]
  have hdet : (τ⁻¹.permMatrix k).det ≠ 0 := by
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ⁻¹) with h | h <;> simp [h]
  let w : GL (Fin N) k := Matrix.GeneralLinearGroup.mkOfDetNeZero (τ⁻¹.permMatrix k) hdet
  have hw : (w : Matrix (Fin N) (Fin N) k) = τ⁻¹.permMatrix k := rfl
  refine ⟨τ⁻¹, w, hw, w⁻¹ * y, ?_, by group⟩
  apply mem_tor_of_offDiag
  intro a b hab
  have hprod : (w : Matrix (Fin N) (Fin N) k) * ((w⁻¹ * y : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      (y : Matrix (Fin N) (Fin N) k) := by
    rw [← Units.val_mul, mul_inv_cancel_left]
  rw [hw, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul] at hprod
  have h1 := congrFun (congrFun hprod (τ a)) b
  simp only [Matrix.submatrix_apply, id] at h1
  have h2 : τ⁻¹ (τ a) = a := by simp
  rw [h2] at h1
  rw [h1]
  apply hzero
  rw [← hτ]
  exact fun e => hab (τ.injective e)

end GlobalTheory.CompanionTheory.LbElem.ConjMonomial

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulInvEqOfCentral
section
open NumberField IsDedekindDomain
open GlobalTheory.CuspRep
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.CentralMult

variable {E : Type} [Field E] [NumberField E] {N : ℕ}

theorem finite_range_inter (C : Set (GA E N)) (hC : IsCompact C) :
    (C ∩ ((ratGL E N).range : Set (GA E N))).Finite := by
  have hd : DiscreteTopology ((ratGL E N).range) := GlobalTheory.MirTower.discrete_of_le_range le_rfl
  have hcl : IsClosed (((ratGL E N).range : Subgroup (GA E N)) : Set (GA E N)) :=
    Subgroup.isClosed_of_discrete
  have hK : IsCompact (C ∩ ((ratGL E N).range : Set (GA E N))) := hC.inter_right hcl
  have hds : DiscreteTopology ↥(C ∩ ((ratGL E N).range : Set (GA E N))) :=
    DiscreteTopology.of_subset hd Set.inter_subset_right
  exact hK.finite ⟨hds⟩

theorem mul_inv_eq_of_central {G : Type} [Group G] {z x a b q r : G} (hz : ∀ g, z * g = g * z)
    (ha : a * x = z * q) (hb : b * x = z * r) : a * b⁻¹ = q * r⁻¹ := by
  have h1 : a = z * q * x⁻¹ := eq_mul_inv_of_mul_eq ha
  have h2 : b = z * r * x⁻¹ := eq_mul_inv_of_mul_eq hb
  have h3 : z * q * x⁻¹ * (z * r * x⁻¹)⁻¹ = z * (q * r⁻¹) * z⁻¹ := by group
  rw [h1, h2, h3, hz, mul_inv_cancel_right]

theorem multC : PositivityTheory.Rg.BcB.E.E3.MultC := by
  intro E _ _ _ N Q hQ
  have hC : IsCompact (Q * Q⁻¹) := hQ.mul hQ.inv
  have hF := finite_range_inter (Q * Q⁻¹) hC
  refine ⟨hF.toFinset.card, fun z hz x => ?_⟩
  rw [← hF.encard_eq_coe_toFinset_card]
  rcases Set.eq_empty_or_nonempty
    {γ : (ratGL E N).range | (γ : GA E N) * x ∈ (fun q => z * q) '' Q} with h0 | ⟨γ₀, q₀, hq₀, e₀⟩
  · rw [h0]
    simp
  · refine Set.encard_le_encard_of_injOn (f := fun γ : (ratGL E N).range => (γ : GA E N) * (γ₀ : GA E N)⁻¹) ?_ ?_
    · rintro γ ⟨q, hq, e⟩
      refine ⟨?_, mul_mem γ.2 (inv_mem γ₀.2)⟩
      have e' : (γ : GA E N) * (γ₀ : GA E N)⁻¹ = q * q₀⁻¹ := mul_inv_eq_of_central hz e.symm e₀.symm
      change (γ : GA E N) * (γ₀ : GA E N)⁻¹ ∈ Q * Q⁻¹
      rw [e']
      exact Set.mul_mem_mul hq (Set.inv_mem_inv.2 hq₀)
    · intro γ _ γ' _ h
      exact Subtype.ext (mul_right_cancel h)

end GlobalTheory.CompanionTheory.CentralMult

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MvecLeviMulUv
section
noncomputable section
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier
namespace GlobalTheory.CompanionTheory.MirLevi
variable {k : Type} [Field k]

def uv (n : ℕ) (v : Fin n → k) : Mir k n := unipIn k n (Multiplicative.ofAdd v)

variable (k) in

def LH (n : ℕ) : Subgroup (Mir k n) := (levi k n).range

variable (k) in

def lv (n : ℕ) : GL (Fin n) k →* LH k n := (levi k n).rangeRestrict

def colv {n : ℕ} (g : Mir k n) : Fin n → k :=
  fun i => ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n)

def mvec {n : ℕ} (g : Mir k n) : Fin n → k :=
  (((mirabolicProjection k n g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec (colv g)

theorem mirProj_levi (n : ℕ) (m : GL (Fin n) k) : mirabolicProjection k n (levi k n m) = m := by
  apply Units.ext
  ext i j
  show GlobalTheory.BZMir.glEmbMat k n (m : Matrix (Fin n) (Fin n) k) (Fin.castSucc i) (Fin.castSucc j) = _
  simp [GlobalTheory.BZMir.glEmbMat]

theorem mirProj_uv (n : ℕ) (v : Fin n → k) : mirabolicProjection k n (uv n v) = 1 := by
  apply Units.ext
  ext i j
  show (1 + GlobalTheory.BZMir.colMat k n v) (Fin.castSucc i) (Fin.castSucc j) = (1 : Matrix (Fin n) (Fin n) k) i j
  simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem coe_levi_mul_uv (n : ℕ) (m : GL (Fin n) k) (v : Fin n → k) :
    (((levi k n m * uv n v : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      glEmbMat k n (m : Matrix (Fin n) (Fin n) k) + colMat k n ((m : Matrix (Fin n) (Fin n) k).mulVec v) := by
  show GlobalTheory.BZMir.glEmbMat k n (m : Matrix (Fin n) (Fin n) k) * (1 + GlobalTheory.BZMir.colMat k n v) = _
  rw [mul_add, mul_one, GlobalTheory.BZMir.glEmbMat_mul_colMat]

theorem colv_levi_mul_uv (n : ℕ) (m : GL (Fin n) k) (v : Fin n → k) :
    colv (levi k n m * uv n v) = (m : Matrix (Fin n) (Fin n) k).mulVec v := by
  funext i
  simp only [GlobalTheory.CompanionTheory.MirLevi.colv]
  rw [GlobalTheory.CompanionTheory.MirLevi.coe_levi_mul_uv]
  simp [GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.colMat]

theorem mvec_levi_mul_uv (n : ℕ) (m : GL (Fin n) k) (v : Fin n → k) :
    mvec (levi k n m * uv n v) = v := by
  unfold GlobalTheory.CompanionTheory.MirLevi.mvec
  rw [GlobalTheory.CompanionTheory.MirLevi.colv_levi_mul_uv, map_mul, GlobalTheory.CompanionTheory.MirLevi.mirProj_levi,
    GlobalTheory.CompanionTheory.MirLevi.mirProj_uv, mul_one, Matrix.mulVec_mulVec, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem decomp {n : ℕ} (g : Mir k n) : g = levi k n (mirabolicProjection k n g) * uv n (mvec g) := by
  have hA : ((GlobalTheory.BZMir.mirabolicProjection k n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec
      (GlobalTheory.CompanionTheory.MirLevi.mvec g) = GlobalTheory.CompanionTheory.MirLevi.colv g := by
    unfold GlobalTheory.CompanionTheory.MirLevi.mvec
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hP : ∀ i j, ((GlobalTheory.BZMir.mirabolicProjection k n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.castSucc j) :=
    fun _ _ => rfl
  have hlast := (GlobalTheory.BZMir.mem_Mir_iff k (g : GL (Fin (n + 1)) k)).1 g.2
  apply Subtype.ext
  apply Units.ext
  rw [GlobalTheory.CompanionTheory.MirLevi.coe_levi_mul_uv, hA]
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [congrFun hlast j]
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.colMat, GlobalTheory.BZMir.eLast]
    · simp [GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.colMat, GlobalTheory.BZMir.eLast, Pi.single_apply,
        Fin.castSucc_ne_last]
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.colMat, GlobalTheory.CompanionTheory.MirLevi.colv]
    · simp [GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.colMat, hP, Fin.castSucc_ne_last]

theorem mvec_uv (n : ℕ) (v : Fin n → k) : mvec (uv n v) = v := by
  have h := GlobalTheory.CompanionTheory.MirLevi.mvec_levi_mul_uv n (1 : GL (Fin n) k) v
  rwa [map_one, one_mul] at h

theorem mvec_levi_mul (n : ℕ) (m : GL (Fin n) k) (g : Mir k n) : mvec (levi k n m * g) = mvec g := by
  conv_lhs => rw [GlobalTheory.CompanionTheory.MirLevi.decomp g, ← mul_assoc, ← map_mul]
  rw [GlobalTheory.CompanionTheory.MirLevi.mvec_levi_mul_uv]

theorem uv_add (n : ℕ) (v w : Fin n → k) : uv n (v + w) = uv n v * uv n w := by
  simp only [GlobalTheory.CompanionTheory.MirLevi.uv, ofAdd_add, map_mul]

theorem uv_zero (n : ℕ) : uv n (0 : Fin n → k) = 1 := by
  simp [GlobalTheory.CompanionTheory.MirLevi.uv]

theorem uv_mul_levi (n : ℕ) (m : GL (Fin n) k) (v : Fin n → k) :
    uv n v * levi k n m = levi k n m * uv n (((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v) := by
  apply Subtype.ext
  have h := GlobalTheory.BZMir.glEmb_mul_unip' k n m
    (Multiplicative.ofAdd (((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v))
  rw [toAdd_ofAdd, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.one_mulVec] at h
  exact h.symm

section Rep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ (LH k n) E)

def restr : cIndSpace (LH k n) ρ →ₗ[ℂ] (Fin n → k) → E where
  toFun f v := f.1.1.1 (uv n v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem restr_injective : Function.Injective (restr ρ) := by
  intro f f' h
  have key : ∀ (F : GlobalTheory.PRep.cIndSpace (GlobalTheory.CompanionTheory.MirLevi.LH k n) ρ)
      (x : GlobalTheory.CompanionTheory.MirLevi.LH k n) (g : GlobalTheory.BZMir.Mir k n),
      F.1.1.1 ((x : GlobalTheory.BZMir.Mir k n) * g) = ρ x (F.1.1.1 g) := by
    intro F x g
    first
    | exact F.1.1.2 x g
    | exact F.1.2 x g
    | exact F.2 x g
    | simpa using F.1.1.2 x g
  have hv : ∀ v, f.1.1.1 (GlobalTheory.CompanionTheory.MirLevi.uv n v) = f'.1.1.1 (GlobalTheory.CompanionTheory.MirLevi.uv n v) :=
    fun v => congrFun h v
  have hall : ∀ g, f.1.1.1 g = f'.1.1.1 g := by
    intro g
    have e : GlobalTheory.BZMir.levi k n (GlobalTheory.BZMir.mirabolicProjection k n g) =
        ((GlobalTheory.CompanionTheory.MirLevi.lv k n (GlobalTheory.BZMir.mirabolicProjection k n g) :
          GlobalTheory.CompanionTheory.MirLevi.LH k n) : GlobalTheory.BZMir.Mir k n) := rfl
    rw [GlobalTheory.CompanionTheory.MirLevi.decomp g, e, key f, key f', hv]
  first
  | exact Subtype.ext (Subtype.ext (Subtype.ext (funext hall)))
  | exact Subtype.ext (Subtype.ext (Subtype.ext (by ext g; exact hall g)))

theorem restr_uv (a : Fin n → k) (f : cIndSpace (LH k n) ρ) (v : Fin n → k) :
    restr ρ (cInd (LH k n) ρ (uv n a) f) v = restr ρ f (v + a) := by
  show f.1.1.1 (GlobalTheory.CompanionTheory.MirLevi.uv n v * GlobalTheory.CompanionTheory.MirLevi.uv n a) = _
  exact congrArg (fun g => f.1.1.1 g) (GlobalTheory.CompanionTheory.MirLevi.uv_add n v a).symm

theorem restr_levi (m : GL (Fin n) k) (f : cIndSpace (LH k n) ρ) (v : Fin n → k) :
    restr ρ (cInd (LH k n) ρ (levi k n m) f) v =
      ρ (lv k n m) (restr ρ f (((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v)) := by
  have key : ∀ (x : GlobalTheory.CompanionTheory.MirLevi.LH k n) (g : GlobalTheory.BZMir.Mir k n),
      f.1.1.1 ((x : GlobalTheory.BZMir.Mir k n) * g) = ρ x (f.1.1.1 g) := by
    intro x g
    first
    | exact f.1.1.2 x g
    | exact f.1.2 x g
    | exact f.2 x g
    | simpa using f.1.1.2 x g
  have e : GlobalTheory.BZMir.levi k n m =
      ((GlobalTheory.CompanionTheory.MirLevi.lv k n m : GlobalTheory.CompanionTheory.MirLevi.LH k n) : GlobalTheory.BZMir.Mir k n) := rfl
  show f.1.1.1 (GlobalTheory.CompanionTheory.MirLevi.uv n v * GlobalTheory.BZMir.levi k n m) = _
  rw [GlobalTheory.CompanionTheory.MirLevi.uv_mul_levi, e, key]
  rfl

end Rep

end GlobalTheory.CompanionTheory.MirLevi
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NatOfSimpleLoweringNilpotent
section
set_option maxSynthPendingDepth 1

noncomputable section

open GroundTheory.Automorphic.HarishChandra

namespace GlobalTheory.CompanionTheory.PresRho

variable {n : ℕ}

theorem e_upper_mul_pow_succ_eq {i j : Fin n} (hij : (j : ℕ) = i + 1) (m : ℕ) :
    e (i, j) * e (j, i) ^ (m + 1) =
      e (j, i) ^ (m + 1) * e (i, j) + ((m : ℂ) + 1) • (e (j, i) ^ m * (e (i, i) - e (j, j))) -
        (((m : ℂ) + 1) * m) • e (j, i) ^ m := by
  have hne : i ≠ j := fun h => by rw [h] at hij; omega
  have hxy : e (i, j) * e (j, i) = e (j, i) * e (i, j) + (e (i, i) - e (j, j)) := by
    have := e_mul_sub_mul (i, j) (j, i)
    simp only [if_true] at this
    rw [← this]; abel
  have hh : ∀ p : ℕ, (e (i, i) - e (j, j)) * e (j, i) ^ p =
      e (j, i) ^ p * (e (i, i) - e (j, j)) - (2 * (p : ℂ)) • e (j, i) ^ p := by
    intro p
    rw [sub_mul, e_diag_mul_e_pow, e_diag_mul_e_pow, rootAt_lower_self hne, rootAt_lower_other hne,
      mul_sub]
    module
  induction m with
  | zero =>
    simp only [pow_zero, pow_one, one_mul, Nat.cast_zero, zero_add, one_smul, mul_zero, zero_smul,
      sub_zero]
    exact hxy
  | succ m ih =>
    have e1 : e (i, j) * e (j, i) ^ (m + 1 + 1) =
        e (j, i) * (e (i, j) * e (j, i) ^ (m + 1)) + (e (i, i) - e (j, j)) * e (j, i) ^ (m + 1) := by
      rw [pow_succ' _ (m + 1), ← mul_assoc, hxy, add_mul, mul_assoc]
    rw [e1, hh, ih]
    simp only [mul_sub, mul_add, mul_smul_comm, ← mul_assoc, ← pow_succ']
    push_cast
    module

theorem h_mul_sub_mem_Jp {μ : Fin n → ℤ} {x : U n} (hx : IsAdW μ x) {i j : Fin n}
    (hij : (j : ℕ) = i + 1) :
    (e (i, i) - e (j, j)) * x - ((1 : ℂ) + (μ i : ℂ) - (μ j : ℂ)) • x ∈ Jp n := by
  have hi := hx i
  have hj := hx j
  have hd := rhoVec_sub (n := n) hij
  have key : (e (i, i) - e (j, j)) * x - ((1 : ℂ) + (μ i : ℂ) - (μ j : ℂ)) • x =
      x * (e (i, i) - algebraMap ℂ (U n) (rhoVec n i)) -
        x * (e (j, j) - algebraMap ℂ (U n) (rhoVec n j)) := by
    have h1 : e (i, i) * x = x * e (i, i) + (μ i : ℂ) • x := by rw [← hi]; abel
    have h2 : e (j, j) * x = x * e (j, j) + (μ j : ℂ) • x := by rw [← hj]; abel
    have h3 : rhoVec n i = rhoVec n j + 1 := by rw [← hd]; ring
    rw [sub_mul, h1, h2]
    simp only [mul_sub, ← Algebra.commutes, ← Algebra.smul_def, h3]
    module
  rw [key]
  exact vermaIdeal_le_Jp (Submodule.sub_mem _ (mul_e_sub_mem_vermaIdeal _ _ i)
    (mul_e_sub_mem_vermaIdeal _ _ j))

theorem natural_of_primitive {n : ℕ} (μ : Fin n → ℤ) (x : U n) (i j : Fin n) (hx : IsAdW μ x)
    (hup : ∀ a : Fin n × Fin n, IsUpper a → e a * x ∈ Jp n) (hxJ : x ∉ Jp n)
    (hij : (j : ℕ) = i + 1) (hN : ∃ N : ℕ, e (j, i) ^ N * x ∈ Jp n) :
    ∃ p : ℕ, 1 + μ i - μ j = (p : ℤ) := by
  classical
  have hp := Nat.find_spec hN
  have hmin := fun m => Nat.find_min hN (m := m)
  obtain ⟨q, hq⟩ : ∃ q, Nat.find hN = q + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun h0 => hxJ ?_
    rw [h0] at hp
    simpa using hp
  rw [hq] at hp
  have hqn : e (j, i) ^ q * x ∉ Jp n := hmin q (by omega)
  have hEx : e (i, j) * x ∈ Jp n := hup (i, j) (by
    simp only [IsUpper]; rw [Fin.lt_def, hij]; omega)
  set c : ℂ := (1 : ℂ) + (μ i : ℂ) - (μ j : ℂ) with hc
  have h1 := mul_mem_Jp (e (i, j)) hp
  have h2 := mul_mem_Jp (e (j, i) ^ (q + 1)) hEx
  have h3 := mul_mem_Jp (e (j, i) ^ q) (h_mul_sub_mem_Jp hx hij)
  have key : (((q : ℂ) + 1) * (c - q)) • (e (j, i) ^ q * x) =
      e (i, j) * (e (j, i) ^ (q + 1) * x) - e (j, i) ^ (q + 1) * (e (i, j) * x) -
        ((q : ℂ) + 1) • (e (j, i) ^ q * ((e (i, i) - e (j, j)) * x - c • x)) := by
    rw [← mul_assoc (e (i, j)), e_upper_mul_pow_succ_eq hij q]
    simp only [mul_sub, sub_mul, add_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]
    module
  have hmem : (((q : ℂ) + 1) * (c - q)) • (e (j, i) ^ q * x) ∈ Jp n := by
    rw [key]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ h1 h2) (Submodule.smul_mem _ _ h3)
  have hzero : ((q : ℂ) + 1) * (c - q) = 0 := by
    by_contra hne
    exact hqn ((Submodule.smul_mem_iff _ hne).1 hmem)
  have hq1 : (q : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero q
  have hcq : c = q := sub_eq_zero.1 ((mul_eq_zero.1 hzero).resolve_left hq1)
  refine ⟨q, ?_⟩
  have : ((1 + μ i - μ j : ℤ) : ℂ) = ((q : ℤ) : ℂ) := by
    push_cast
    exact hcq
  exact_mod_cast this

end GlobalTheory.CompanionTheory.PresRho
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductSingleNonzeroFactorEquiv
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.FineProd.ProdSingle

theorem prodIrr_single : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (Y : Fin h → IrrGL k) (hd : ∑ a, (Y a).1 = N) (i₀ : Fin h), (∀ i, i ≠ i₀ → (Y i).1 = 0) → ∃ z : IrrCl (GL (Fin N) k), (⟨N, z⟩ : IrrGL k) = Y i₀ ∧ Nonempty ((prodIrr Y hd).Equiv z.rep.ρ) := by
  intro k _ _ _ _ h N Y hd i₀ h0
  have hN : (Y i₀).1 = N := by
    rw [← hd]
    exact (Finset.sum_eq_single i₀ (fun i _ hi => h0 i hi) (fun hi => absurd (Finset.mem_univ _) hi)).symm
  subst hN
  refine ⟨(Y i₀).2, Sigma.eta _, ?_⟩
  have hd' : ∑ a : Fin 1, (Y ((fun _ : Fin 1 => i₀) a)).1 = (Y i₀).1 := by simp
  obtain ⟨e₁⟩ := GlobalTheory.T.induced_product_drop_zero_factors Y hd (fun _ : Fin 1 => i₀) (Subsingleton.strictMono _)
    (fun j hj => ⟨0, by
      by_contra hne
      exact hj (h0 j (fun e => hne e.symm))⟩) hd'
  obtain ⟨e₂⟩ := nonempty_equiv_prodIrr_one (Y i₀) hd'
  exact ⟨e₁.trans e₂.symm⟩

end GlobalTheory.CompanionTheory.FineProd.ProdSingle
end

