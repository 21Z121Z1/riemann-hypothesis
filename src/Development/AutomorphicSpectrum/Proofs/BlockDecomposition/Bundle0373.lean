import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0369
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0364
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjacentDescentOrOpenCell
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier

theorem antitone_comp_of_adjacent {h N : ℕ} (b : Fin N → Fin h) (w : Equiv.Perm (Fin N))
    (hstep : ∀ i j : Fin N, (j : ℕ) = i + 1 → b (w j) ≤ b (w i)) :
    Antitone (b ∘ w) := by
  intro x y hxy
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  simp only [Fin.mk_le_mk] at hxy
  revert hy
  induction y, hxy using Nat.le_induction with
  | base => intro hy; exact le_rfl
  | succ n hxn ih =>
    intro hy
    have hn : n < N := by omega
    exact le_trans (hstep ⟨n, hn⟩ ⟨n + 1, hy⟩ rfl) (ih hn)

theorem blk_comp_wOpen_antitone {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) :
    Antitone (blk (stdBlocks d hd) ∘ wOpen d hd) := by
  intro x y hxy
  have hm := Tuple.monotone_sort (wKey d hd) hxy
  simp only [Function.comp, wKey] at hm
  rcases Prod.Lex.toLex_le_toLex.mp hm with h | ⟨h, -⟩
  · exact (OrderDual.toDual_lt_toDual.mp h).le
  · exact le_of_eq (OrderDual.toDual_inj.mp h).symm

theorem pm_mem_parab_of_blk_eq (k : Type) [Field k] {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)
    (v : Equiv.Perm (Fin N)) (hv : ∀ q, blk (stdBlocks d hd) (v q) = blk (stdBlocks d hd) q) :
    pm k v ∈ parab k (stdBlocks d hd) := by
  show (↑(pm k v) : Matrix (Fin N) (Fin N) k).BlockTriangular (blk (stdBlocks d hd))
  intro i j hij
  have hne : v⁻¹ i ≠ j := by
    intro hj
    subst hj
    have hb := hv (v⁻¹ i)
    have hvi : v (v⁻¹ i) = i := by simp
    rw [hvi] at hb
    rw [← hb] at hij
    exact lt_irrefl _ hij
  change (Equiv.toPEquiv v⁻¹).toMatrix i j = 0
  rw [PEquiv.toMatrix_apply]
  simpa using hne

theorem cell_eq_of_blk_eq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)
    (w w' : Equiv.Perm (Fin N))
    (hw : ∀ p, blk (stdBlocks d hd) (w p) = blk (stdBlocks d hd) (w' p)) :
    cell k d hd w = cell k d hd w' := by
  have key : ∀ u u' : Equiv.Perm (Fin N),
      (∀ p, blk (stdBlocks d hd) (u p) = blk (stdBlocks d hd) (u' p)) → cell k d hd u ⊆ cell k d hd u' := by
    intro u u' hu g hg
    simp only [cell, Set.mem_ofPred_eq] at hg ⊢
    obtain ⟨p, hp, n, hn, rfl⟩ := hg
    have hv : ∀ q, blk (stdBlocks d hd) ((u * u'⁻¹) q) = blk (stdBlocks d hd) q := by
      intro q
      rw [Equiv.Perm.mul_apply, hu]
      simp
    have hpm : pm k u = pm k (u * u'⁻¹) * pm k u' := by
      unfold pm
      rw [← map_mul, inv_mul_cancel_right]
    refine ⟨p * pm k (u * u'⁻¹), (parab k (stdBlocks d hd)).mul_mem hp (pm_mem_parab_of_blk_eq k d hd _ hv),
      n, hn, ?_⟩
    rw [hpm]
    simp only [mul_assoc]
  exact Set.Subset.antisymm (key w w' hw) (key w' w fun p => (hw p).symm)

theorem exists_adjacent_blk_lt_or_cell_eq_open : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (w : Equiv.Perm (Fin N)),
    (∃ i j : Fin N, (j : ℕ) = i + 1 ∧ blk (stdBlocks d hd) (w i) < blk (stdBlocks d hd) (w j)) ∨
      cell k d hd w = cell k d hd (wOpen d hd) := by
  intro k _ _ _ _ h N d hd w
  by_cases hex : ∃ i j : Fin N, (j : ℕ) = i + 1 ∧ blk (stdBlocks d hd) (w i) < blk (stdBlocks d hd) (w j)
  · exact Or.inl hex
  · right
    simp only [not_exists, not_and, not_lt] at hex
    have hA := antitone_comp_of_adjacent (blk (stdBlocks d hd)) w hex
    have hB := blk_comp_wOpen_antitone d hd
    have hU := Tuple.unique_monotone (f := fun q => OrderDual.toDual (blk (stdBlocks d hd) q))
      (σ := w) (τ := wOpen d hd) (monotone_toDual_comp_iff.mpr hA) (monotone_toDual_comp_iff.mpr hB)
    refine cell_eq_of_blk_eq k d hd w (wOpen d hd) fun p => ?_
    exact OrderDual.toDual_inj.mp (congrFun hU p)

end GlobalTheory.CompanionTheory.Rodier
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatCellHeightStratification
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.Parabolic DoubleCoset

namespace GlobalTheory.CompanionTheory.Rodier.CellOrder

def blkNat {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (i : Fin N) : ℕ :=
  ((blk (stdBlocks d hd) i : Fin h) : ℕ)

def idxNat {N : ℕ} (i : Fin N) : ℕ := i

theorem card_filter_le_of_antitone {N : ℕ} (β : Fin N → ℕ) (u w : Equiv.Perm (Fin N))
    (hu : Antitone (β ∘ u)) (a b : ℕ) :
    (Finset.univ.filter fun j : Fin N => (j : ℕ) ≤ b ∧ a ≤ β (w j)).card ≤
      (Finset.univ.filter fun j : Fin N => (j : ℕ) ≤ b ∧ a ≤ β (u j)).card := by
  classical
  by_cases hsub : ∀ j : Fin N, (j : ℕ) ≤ b → a ≤ β (u j)
  · apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact ⟨hj.1, hsub j hj.1⟩
  · push Not at hsub
    obtain ⟨i, hib, hia⟩ := hsub
    have hdown : ∀ j : Fin N, a ≤ β (u j) → (j : ℕ) ≤ b := by
      intro j hj
      by_contra hjb
      push Not at hjb
      have hij : i ≤ j := by
        rw [Fin.le_iff_val_le_val]
        omega
      exact absurd (le_trans hj (hu hij)) (not_le.2 hia)
    have e1 : (Finset.univ.filter fun j : Fin N => (j : ℕ) ≤ b ∧ a ≤ β (u j)) =
        Finset.univ.filter fun j : Fin N => a ≤ β (u j) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨hdown j h, h⟩⟩
    rw [e1]
    calc (Finset.univ.filter fun j : Fin N => (j : ℕ) ≤ b ∧ a ≤ β (w j)).card
        ≤ (Finset.univ.filter fun j : Fin N => a ≤ β (w j)).card := by
          apply Finset.card_le_card
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
          exact hj.2
      _ = (Finset.univ.filter fun j : Fin N => a ≤ β (u j)).card := by
          apply Finset.card_bij' (fun j _ => u.symm (w j)) (fun j _ => w.symm (u j)) <;> simp_all

theorem exists_diag_mul_unip {k : Type} [Field k] {N : ℕ} (b : GL (Fin N) k)
    (hb : b ∈ blockUpper k N (idxNat (N := N))) :
    ∃ t : GL (Fin N) k, (∀ i j, i ≠ j → (t : Matrix (Fin N) (Fin N) k) i j = 0) ∧
      ∃ n ∈ unipB k (Fin N), b = t * n := by
  classical
  have hb' : (b : Matrix (Fin N) (Fin N) k).BlockTriangular id := fun i j h => hb h
  have hdet : ∏ i, (b : Matrix (Fin N) (Fin N) k) i i ≠ 0 := by
    rw [← Matrix.det_of_upperTriangular hb']
    exact (Matrix.isUnits_det_units b).ne_zero
  have hD : ∀ i, (b : Matrix (Fin N) (Fin N) k) i i ≠ 0 :=
    fun i => (Finset.prod_ne_zero_iff.1 hdet) i (Finset.mem_univ i)
  let D : Fin N → k := fun i => (b : Matrix (Fin N) (Fin N) k) i i
  let t : GL (Fin N) k := ⟨Matrix.diagonal D, Matrix.diagonal D⁻¹, by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact mul_inv_cancel₀ (hD i), by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact inv_mul_cancel₀ (hD i)⟩
  refine ⟨t, fun i j hij => Matrix.diagonal_apply_ne _ hij, t⁻¹ * b, ?_, (mul_inv_cancel_left t b).symm⟩
  have hval : ((t⁻¹ * b : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal D⁻¹ * (b : Matrix (Fin N) (Fin N) k) := rfl
  have hP : ((t⁻¹ * b : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).BlockTriangular
      (GlobalTheory.SmGL.blk (GlobalTheory.SmGL.points (Fin N))) := by
    rw [hval]
    exact (Matrix.blockTriangular_diagonal _).mul (fun i j h => hb h)
  show t⁻¹ * b ∈ GlobalTheory.SmGL.unipRad k (GlobalTheory.SmGL.points (Fin N))
  unfold GlobalTheory.SmGL.unipRad
  rw [Subgroup.mem_map]
  refine ⟨⟨t⁻¹ * b, hP⟩, ?_, rfl⟩
  rw [MonoidHom.mem_ker]
  funext a
  apply Units.ext
  ext x y
  change ((t⁻¹ * b : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) a a = (1 : Matrix Unit Unit k) x y
  rw [hval, Matrix.diagonal_mul, Subsingleton.elim x y, Matrix.one_apply_eq]
  exact inv_mul_cancel₀ (hD a)

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem parab_eq_blockUpper :
    parab k (stdBlocks d hd) = blockUpper k N (blkNat d hd) := by
  ext g
  exact Iff.rfl

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem unipB_le_blockUpper : unipB k (Fin N) ≤ blockUpper k N (idxNat (N := N)) := by
  intro g hg
  obtain ⟨p, -, rfl⟩ := Subgroup.mem_map.1 hg
  exact fun i j h => p.2 h

theorem cell_eq_doubleCoset (w : Equiv.Perm (Fin N)) :
    cell k d hd w = doubleCoset (pm k w) (blockUpper k N (blkNat d hd) : Set (GL (Fin N) k))
      (blockUpper k N (idxNat (N := N))) := by
  ext g
  rw [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨p, hp, n, hn, rfl⟩
    rw [parab_eq_blockUpper] at hp
    exact ⟨p, hp, n, unipB_le_blockUpper k hn, rfl⟩
  · rintro ⟨p, hp, q, hq, rfl⟩
    obtain ⟨t, ht, n, hn, rfl⟩ := exists_diag_mul_unip q hq
    refine ⟨p * (pm k w * t * (pm k w)⁻¹), ?_, n, hn, by group⟩
    rw [parab_eq_blockUpper]
    refine Subgroup.mul_mem _ hp ?_
    unfold pm
    rw [GroundTheory.Automorphic.Parabolic.conj_permGL_mem_blockUpper_iff]
    intro i j hij
    exact ht i j (fun h => by subst h; exact lt_irrefl _ hij)

theorem antitone_blkNat_wOpen : Antitone (blkNat d hd ∘ wOpen d hd) := by
  intro i j hij
  have hm := Tuple.monotone_sort (wKey d hd) hij
  simp only [Function.comp_apply] at hm ⊢
  unfold wOpen blkNat
  unfold wKey at hm
  rcases (Prod.Lex.toLex_le_toLex).1 hm with h1 | ⟨h1, -⟩
  · exact (Fin.lt_def.1 (OrderDual.toDual_lt_toDual.1 h1)).le
  · exact le_of_eq (congrArg Fin.val (OrderDual.toDual_inj.1 h1)).symm

theorem cellRank_le_wOpen (w : Equiv.Perm (Fin N)) (a b : ℕ) :
    cellRank (blkNat d hd) idxNat (pm k w) a b ≤
      cellRank (blkNat d hd) idxNat (pm k (wOpen d hd)) a b := by
  unfold pm
  rw [GroundTheory.Automorphic.Parabolic.cellRank_permGL, GroundTheory.Automorphic.Parabolic.cellRank_permGL]
  exact card_filter_le_of_antitone (blkNat d hd) (wOpen d hd) w (antitone_blkNat_wOpen d hd) a b

theorem cells_cover_height :
    (∀ g : GL (Fin N) k, ∃ w, g ∈ cell k d hd w) ∧ ∃ ht : GL (Fin N) k → ℕ,
      (∀ w, ∀ g ∈ cell k d hd w, ht g = ht (pm k w)) ∧
      (∀ w, closure (cell k d hd w) ⊆ cell k d hd w ∪ {x | ht x < ht (pm k w)}) ∧
      ∀ w, cell k d hd w ≠ cell k d hd (wOpen d hd) → ht (pm k w) < ht (pm k (wOpen d hd)) := by
  refine ⟨fun g => ?_, GroundTheory.Automorphic.Parabolic.cellHeight (blkNat d hd) idxNat, fun w g hg => ?_,
    fun w => ?_, fun w hw => ?_⟩
  · obtain ⟨w, hw⟩ := GroundTheory.Automorphic.Parabolic.exists_permGL_mem_doubleCoset
      (F := k) (β := blkNat d hd) (γ := idxNat) g
    refine ⟨w, ?_⟩
    rw [cell_eq_doubleCoset]
    exact hw
  · rw [cell_eq_doubleCoset] at hg
    exact GroundTheory.Automorphic.Parabolic.cellHeight_of_mem_doubleCoset hg
  · rw [cell_eq_doubleCoset]
    exact GroundTheory.Automorphic.Parabolic.closure_doubleCoset_subset _
  · by_contra hle
    push Not at hle
    have hr := GroundTheory.Automorphic.Parabolic.cellRank_eq_of_le_of_cellHeight_le
      (fun a b => cellRank_le_wOpen k d hd w a b) hle
    have hmem := GroundTheory.Automorphic.Parabolic.mem_doubleCoset_of_cellRank_eq hr
    apply hw
    rw [cell_eq_doubleCoset, cell_eq_doubleCoset, DoubleCoset.doubleCoset_eq_of_mem hmem]

theorem cells_main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ g : GL (Fin N) k, ∃ w, g ∈ cell k d hd w) ∧ ∃ ht : GL (Fin N) k → ℕ, (∀ w, ∀ g ∈ cell k d hd w, ht g = ht (pm k w)) ∧ (∀ w, closure (cell k d hd w) ⊆ cell k d hd w ∪ {x | ht x < ht (pm k w)}) ∧ ∀ w, cell k d hd w ≠ cell k d hd (wOpen d hd) → ht (pm k w) < ht (pm k (wOpen d hd)) := by
  intro k _ _ _ _ h N d hd
  exact cells_cover_height k d hd

end GlobalTheory.CompanionTheory.Rodier.CellOrder
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliAuxiliaryStatement
section
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Matrix Topology

namespace GlobalTheory.CompanionTheory.CTFin.CapRes

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a b n : ℕ}

theorem map_emb₂ {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (e : Fin a ⊕ Fin b ≃ Fin n)
    (g : GL (Fin a) R × GL (Fin b) R) :
    GeneralLinearGroup.map f (GlobalTheory.SmGL.emb₂ R e g) =
      GlobalTheory.SmGL.emb₂ S e (GeneralLinearGroup.map f g.1, GeneralLinearGroup.map f g.2) := by
  apply Units.ext
  ext p q
  obtain ⟨p, rfl⟩ := e.surjective p
  obtain ⟨q, rfl⟩ := e.surjective q
  change f ((GlobalTheory.SmGL.emb₂ R e g : Matrix _ _ R) (e p) (e q)) = (GlobalTheory.SmGL.emb₂ S e _ : Matrix _ _ S) (e p) (e q)
  rw [GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.val_emb₂]
  rcases p with p | p <;> rcases q with q | q <;> simp

theorem emb₂_swap {R : Type} [CommRing R] (e : Fin a ⊕ Fin b ≃ Fin n) (g₁ : GL (Fin a) R) (g₂ : GL (Fin b) R) :
    GlobalTheory.SmGL.emb₂ R ((Equiv.sumComm (Fin b) (Fin a)).trans e) (g₂, g₁) = GlobalTheory.SmGL.emb₂ R e (g₁, g₂) := by
  apply Units.ext
  rw [GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.val_emb₂]
  ext p q
  obtain ⟨p, rfl⟩ := e.surjective p
  obtain ⟨q, rfl⟩ := e.surjective q
  rcases p with p | p <;> rcases q with q | q <;> simp

theorem emb_infGL (e : Fin a ⊕ Fin b ≃ Fin n) (y : GL (Fin a) (Cinf E)) :
    GlobalTheory.SmGL.emb₂ (Ad E) e (infGL E a y, (1 : GL (Fin b) (Ad E))) =
      infGL E n (GlobalTheory.SmGL.emb₂ (Cinf E) e (y, 1)) := by
  refine ga_ext ?_ ?_
  · rw [pInf_infGL, map_emb₂]; simp
  · rw [pFin_infGL, map_emb₂, pFin_infGL, map_one]
    exact map_one _

def blockL (e : Fin a ⊕ Fin b ≃ Fin n) : Lie E a →L[ℝ] Lie E n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => toL (reindex e e (fromBlocks (Matrix.of x) 0 0 0))
      map_add' := fun x y => by
        funext p q
        obtain ⟨p, rfl⟩ := e.surjective p
        obtain ⟨q, rfl⟩ := e.surjective q
        rcases p with p | p <;> rcases q with q | q <;> simp
      map_smul' := fun c x => by
        funext p q
        obtain ⟨p, rfl⟩ := e.surjective p
        obtain ⟨q, rfl⟩ := e.surjective q
        rcases p with p | p <;> rcases q with q | q <;> simp }

theorem blockL_apply (e : Fin a ⊕ Fin b ≃ Fin n) (x : Lie E a) (p q : Fin a ⊕ Fin b) :
    blockL e x (e p) (e q) = fromBlocks (Matrix.of x) 0 0 0 p q := by
  simp [blockL]

def shift (e : Fin a ⊕ Fin b ≃ Fin n) (x : Lie E a) : Lie E n := (oneL E n - blockL e (oneL E a)) + blockL e x

theorem shift_one (e : Fin a ⊕ Fin b ≃ Fin n) : shift e (oneL E a) = oneL E n := by simp [shift]

theorem toL_emb (e : Fin a ⊕ Fin b ≃ Fin n) (y : GL (Fin a) (Cinf E)) :
    toL (GlobalTheory.SmGL.emb₂ (Cinf E) e (y, 1)).val = shift e (toL y.val) := by
  rw [GlobalTheory.SmGL.val_emb₂]
  funext p q
  obtain ⟨p, rfl⟩ := e.surjective p
  obtain ⟨q, rfl⟩ := e.surjective q
  simp only [shift, Pi.add_apply, Pi.sub_apply, blockL_apply]
  rcases p with p | p <;> rcases q with q | q <;> simp [Matrix.one_apply]

theorem blockL_single (e : Fin a ⊕ Fin b ≃ Fin n) (i j : Fin a) (x : Cinf E) :
    blockL e (toL (Matrix.single i j x)) = toL (Matrix.single (e (.inl i)) (e (.inl j)) x) := by
  funext p q
  obtain ⟨p, rfl⟩ := e.surjective p
  obtain ⟨q, rfl⟩ := e.surjective q
  rw [blockL_apply]
  change fromBlocks (Matrix.single i j x) 0 0 0 p q = Matrix.single (e (.inl i)) (e (.inl j)) x (e p) (e q)
  rcases p with p | p <;> rcases q with q | q <;> simp [Matrix.single_apply]

def iota (e : Fin a ⊕ Fin b ≃ Fin n) : GA E a →* GA E n :=
  (GlobalTheory.SmGL.emb₂ (Ad E) e).comp (MonoidHom.inl _ _)

theorem iota_apply (e : Fin a ⊕ Fin b ≃ Fin n) (m : GA E a) : iota e m = GlobalTheory.SmGL.emb₂ (Ad E) e (m, 1) := rfl

theorem chart_eq (e : Fin a ⊕ Fin b ≃ Fin n) {F : GA E n → ℂ} {G : GA E a → ℂ} (h : ∀ m, G m = F (iota e m))
    (m : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) : chart G m x = chart F (iota e m) (shift e x) := by
  obtain ⟨u, hu⟩ := id hx
  have e1 : x = toL u.val := hu.symm
  subst e1
  rw [chart_val, h, map_mul, ← toL_emb, chart_val, iota_apply e (infGL E a u), emb_infGL]

theorem lieD_eq (e : Fin a ⊕ Fin b ≃ Fin n) {F : GA E n → ℂ} (hF : F ∈ Sm E n) {G : GA E a → ℂ}
    (h : ∀ m, G m = F (iota e m)) (X : Lie E a) (m : GA E a) :
    lieD X G m = lieD (blockL e X) F (iota e m) := by
  have hd : HasFDerivAt (shift e) (blockL e : Lie E a →L[ℝ] Lie E n) (oneL E a) :=
    (blockL e).hasFDerivAt.const_add _
  have hc : HasFDerivAt (chart F (iota e m)) (fderiv ℝ (chart F (iota e m)) (oneL E n)) (shift e (oneL E a)) := by
    rw [shift_one]; exact (differentiableAt_chart hF _).hasFDerivAt
  have h2 := hc.comp (oneL E a) hd
  have h3 : chart G m =ᶠ[𝓝 (oneL E a)] chart F (iota e m) ∘ shift e := by
    filter_upwards [isOpen_invSet.mem_nhds (show oneL E a ∈ invSet E a from isUnit_one)] with x hx
    exact chart_eq e h m hx
  unfold lieD
  rw [h3.fderiv_eq, h2.fderiv]
  rfl

def relAlg (e : Fin a ⊕ Fin b ≃ Fin n) : Subalgebra ℂ (Module.End ℂ (Sm E a) × Module.End ℂ (Sm E n)) where
  carrier := {p | ∀ (F : Sm E n) (G : Sm E a), (∀ m, G.1 m = F.1 (iota e m)) →
    ∀ m, (p.1 G).1 m = (p.2 F).1 (iota e m)}
  mul_mem' := fun hp hq F G h m => hp _ _ (hq F G h) m
  add_mem' := fun hp hq F G h m => congrArg₂ (· + ·) (hp F G h m) (hq F G h m)
  algebraMap_mem' := fun c F G h m => congrArg (c • ·) (h m)

theorem lie_mem (e : Fin a ⊕ Fin b ≃ Fin n) (X : Lie E a) :
    ((lie E a X, lie E n (blockL e X)) : Module.End ℂ (Sm E a) × Module.End ℂ (Sm E n)) ∈ relAlg e :=
  fun F _ h m => lieD_eq e F.2 h X m

theorem lieS_mem (e : Fin a ⊕ Fin b ≃ Fin n) (i j : Fin a) (x : Cinf E) :
    ((lieS E a i j x, lieS E n (e (.inl i)) (e (.inl j)) x) : Module.End ℂ (Sm E a) × Module.End ℂ (Sm E n)) ∈
      relAlg e := by
  have := lie_mem e (toL (Matrix.single i j x))
  rwa [blockL_single] at this

theorem Eop_mem (e : Fin a ⊕ Fin b ≃ Fin n) (τ : E →+* ℂ) (i j : Fin a) :
    ((Eop τ i j, Eop τ (e (.inl i)) (e (.inl j))) : Module.End ℂ (Sm E a) × Module.End ℂ (Sm E n)) ∈ relAlg e :=
  (relAlg e).smul_mem ((relAlg e).sub_mem (lieS_mem e i j _) ((relAlg e).smul_mem (lieS_mem e i j _) _)) _

theorem qdet_mem (e : Fin a ⊕ Fin b ≃ Fin n) (τ : E →+* ℂ) (v : ℂ) :
    ((Formalism.REAL.qdet (Eop τ) v, Formalism.REAL.qdet (fun i j : Fin a => Eop τ (e (.inl i)) (e (.inl j))) v) :
      Module.End ℂ (Sm E a) × Module.End ℂ (Sm E n)) ∈ relAlg e := by
  let P := Module.End ℂ (Sm E a) × Module.End ℂ (Sm E n)
  let Z : Fin a → Fin a → P := fun i j => (Eop τ i j, Eop τ (e (.inl i)) (e (.inl j)))
  have h1 := map_qdet (AlgHom.fst ℂ (Module.End ℂ (Sm E a)) (Module.End ℂ (Sm E n))) Z v
  have h2 := map_qdet (AlgHom.snd ℂ (Module.End ℂ (Sm E a)) (Module.End ℂ (Sm E n))) Z v
  have h3 : Formalism.REAL.qdet Z v ∈ relAlg e := by
    refine (relAlg e).sum_mem fun σ _ => (relAlg e).mul_mem (intCast_mem (relAlg e) _)
      ((relAlg e).list_prod_mem fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine (relAlg e).add_mem ?_ (Eop_mem e τ _ _)
    split_ifs
    · exact (relAlg e).algebraMap_mem _
    · exact (relAlg e).zero_mem
  convert h3 using 1
  exact Prod.ext h1.symm h2.symm

theorem aeval_mem (e : Fin a ⊕ Fin b ≃ Fin n) {z : Module.End ℂ (Sm E a)} {z' : Module.End ℂ (Sm E n)}
    (hz : (z, z') ∈ relAlg e) (q : Polynomial ℂ) :
    (Polynomial.aeval z q, Polynomial.aeval z' q) ∈ relAlg e := by
  have h1 := Polynomial.aeval_algHom_apply (AlgHom.fst ℂ (Module.End ℂ (Sm E a)) (Module.End ℂ (Sm E n))) (z, z') q
  have h2 := Polynomial.aeval_algHom_apply (AlgHom.snd ℂ (Module.End ℂ (Sm E a)) (Module.End ℂ (Sm E n))) (z, z') q
  have h3 : Polynomial.aeval (z, z') q ∈ relAlg e := by
    rw [Polynomial.aeval_eq_sum_range]
    exact (relAlg e).sum_mem fun i _ => (relAlg e).smul_mem ((relAlg e).pow_mem hz i) _
  convert h3 using 1
  exact Prod.ext h1 h2

end GlobalTheory.CompanionTheory.CTFin.CapRes

namespace GlobalTheory.CompanionTheory.CTFin

open CapRes

theorem capelli_restrict : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) (q : Polynomial ℂ) (F : Sm E (r + s)), (∀ G : Sm E r, (∀ m, G.1 m = F.1 (lev (Ad E) r s (m, 1))) → ∀ m, (Polynomial.aeval (cap (a := r) τ u) q G).1 m = (Polynomial.aeval (capR r s τ u) q F).1 (lev (Ad E) r s (m, 1))) ∧ (∀ G : Sm E s, (∀ m, G.1 m = F.1 (lev (Ad E) r s (1, m))) → ∀ m, (Polynomial.aeval (cap (a := s) τ u) q G).1 m = (Polynomial.aeval (capS r s τ u) q F).1 (lev (Ad E) r s (1, m))) := by
  intro E _ _ _ r s τ u q F
  constructor
  · intro G h m
    exact aeval_mem (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) (qdet_mem _ τ _) q F G h m
  · intro G h m
    have hι : ∀ m : GA E s, iota ((Equiv.sumComm (Fin s) (Fin r)).trans (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))) m =
        lev (Ad E) r s (1, m) := fun m => emb₂_swap _ _ _
    have := aeval_mem ((Equiv.sumComm (Fin s) (Fin r)).trans (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)))
      (qdet_mem _ τ (u + ((s : ℂ) - 1) / 2)) q F G (fun m => by rw [hι]; exact h m) m
    rw [hι] at this
    exact this

end GlobalTheory.CompanionTheory.CTFin

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterExists
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.ScalarEx

theorem exists_scalarBy : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : IrrGL k) (t : kˣ), ∃ c : ℂ, Zl.ScalarBy x t c := by
  intro k _ _ _ _ x t
  obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar x.2.rep.smooth x.2.rep.irr
  exact ⟨(ω t : ℂ), fun v => hω t v⟩

end GlobalTheory.CompanionTheory.ScalarEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterTwistAbsPow
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.Dblock

theorem smul_of_equiv_nu {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W} (φ : π.Equiv σ) (g : G) (c : ℂ)
    (h : ∀ v, π g v = c • v) (w : W) : σ g w = c • w := by
  rw [← Representation.Equiv.conj_apply_self g φ, LinearEquiv.conj_apply]
  simp [h]
  congr 1
  exact φ.right_inv w

theorem scalarBy_nu : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : IrrGL k) (s : ℂ) (t : kˣ) (c : ℂ), Zl.ScalarBy x t c →
      Zl.ScalarBy (x.nu s) t (c * ((absPow k s (t ^ x.1) : ℂˣ) : ℂ)) := by
  intro k _ _ _ _ x s t c hx v
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin x.1) t) = t ^ x.1 := by
    ext
    simp [Matrix.GeneralLinearGroup.scalar]
  refine smul_of_equiv_nu (x.twEquiv (absPow k s) (isSmoothChar_absPow s))
    (Matrix.GeneralLinearGroup.scalar (Fin x.1) t) _ (fun u => ?_) v
  rw [GlobalTheory.SmGL.twist_apply, GlobalTheory.SmGL.detChar_apply, hx u, smul_smul, hdet, mul_comm]

end GlobalTheory.CompanionTheory.Dblock
end

