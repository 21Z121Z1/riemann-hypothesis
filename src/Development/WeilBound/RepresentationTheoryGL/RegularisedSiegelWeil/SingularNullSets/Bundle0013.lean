import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0012
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0346
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0011
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0008
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWA
section
noncomputable section

set_option synthInstance.maxHeartbeats 200000

open scoped Matrix TensorProduct
open IsDedekindDomain NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.AdelicU
  GlobalTheory.MixModel GlobalTheory.StdUnn Filter MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.L.LFixW

variable {D : D7} {S : Finset (Pl D)} {e : AE D} {a b : ℕ}

theorem idem_in (he : IsIdem S e) {v : Pl D} (hv : v ∈ S) : cv D v e = 1 := by rw [he.2 v, if_pos hv]

theorem idem_out (he : IsIdem S e) {v : Pl D} (hv : v ∉ S) : cv D v e = 0 := by rw [he.2 v, if_neg hv]

theorem idem_mul_offS (he : IsIdem S e) {z : AE D} (hz : OffS S z) : e * z = 0 := by
  refine LIdemEx.ae_ext _ _ (fun w => ?_) (fun v => ?_)
  · rw [map_mul, hz.1 w, mul_zero, map_zero]
  · rw [map_mul, map_zero]
    by_cases hv : v ∈ S
    · rw [hz.2.1 v hv, mul_zero]
    · rw [idem_out he hv, zero_mul]

theorem offS_sub_idem (he : IsIdem S e) {x : AE D} (hx : IntS S x) : OffS S (x - e * x) := by
  refine ⟨fun w => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · rw [RingHom.map_sub, RingHom.map_mul, he.1 w, one_mul, sub_self]
  · rw [RingHom.map_sub, RingHom.map_mul, idem_in he hv, one_mul, sub_self]
  · have h := hx v hv
    rw [RingHom.map_sub, RingHom.map_mul, idem_out he hv, zero_mul, sub_zero]
    exact h

def OffM (S : Finset (Pl D)) (z : Mx D a b) : Prop := ∀ i j, OffS S (z i j)

theorem good_supp {Φ : Mx D a b → ℂ} (hΦ : Good S e Φ) {x : Mx D a b} (hx : ¬ IntOff S x) : Φ x = 0 := by
  rw [hΦ x, if_neg hx]

theorem good_shift (he : IsIdem S e) {Φ : Mx D a b → ℂ} (hΦ : Good S e Φ) (x : Mx D a b) {z : Mx D a b}
    (hz : OffM S z) : Φ (x + z) = Φ x := by
  have h1 : IntOff S (x + z) ↔ IntOff S x := by
    rw [intOff_iff, intOff_iff]
    constructor
    · intro h i j
      have := (h i j).add (hz i j).intS.neg
      rwa [Matrix.add_apply, add_neg_cancel_right] at this
    · intro h i j
      rw [Matrix.add_apply]
      exact (h i j).add (hz i j).intS
  have h2 : e • (x + z) = e • x := by
    have : e • z = 0 := by
      ext i j
      rw [Matrix.smul_apply, smul_eq_mul, idem_mul_offS he (hz i j)]
      rfl
    rw [smul_add, this, add_zero]
  rw [hΦ (x + z), hΦ x, h1, h2]

theorem good_of (he : IsIdem S e) {Φ : Mx D a b → ℂ} (hs : ∀ x, ¬ IntOff S x → Φ x = 0)
    (ht : ∀ x z, OffM S z → Φ (x + z) = Φ x) : Good S e Φ := by
  intro x
  split_ifs with h
  · have hz : OffM S (x - e • x) := fun i j => by
      rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      exact offS_sub_idem he ((intOff_iff x).1 h i j)
    have := ht (e • x) (x - e • x) hz
    rw [add_sub_cancel] at this
    exact this
  · exact hs x h

def kap {r n : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (Q : Matrix (Fin r) (Fin r) D.host.E) (x y : Mx D r n) : ℂ :=
  ψ (trA (Matrix.trace (adj x * (rat Q * y))))

variable {r : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {Q : Matrix (Fin r) (Fin r) D.host.E}

theorem trA_add (z z' : AE D) : trA (z + z') = trA z + trA z' := map_add (Algebra.trace (AF D.host.F) (AE D)) z z'

theorem kap_add_right {n : ℕ} (x y z : Mx D r n) : kap ψ Q x (y + z) = kap ψ Q x y * kap ψ Q x z := by
  unfold kap
  rw [Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, trA_add, AddChar.map_add_eq_mul]

theorem kap_add_left {n : ℕ} (x y z : Mx D r n) : kap ψ Q (x + z) y = kap ψ Q x y * kap ψ Q z y := by
  unfold kap
  rw [adj_add, Matrix.add_mul, Matrix.trace_add, trA_add, AddChar.map_add_eq_mul]

theorem kap_one (Q : Matrix (Fin r) (Fin r) D.host.E) (hψ : IsCharAF D.host.F ψ) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ (n : ℕ) (x z : Mx D r n), IntOff S x → OffM S z →
      kap ψ Q x z = 1 ∧ kap ψ Q z x = 1 := by
  classical
  obtain ⟨S₁, hS₁⟩ := exists_rat_int Q
  obtain ⟨S₂, hS₂⟩ := psi_off hψ
  refine ⟨S₁ ∪ S₂, fun S hS n x z hx hz => ⟨?_, ?_⟩⟩
  · have hQ := hS₁ S (fun v h => hS (Finset.mem_union_left _ h))
    have hx' := (intOff_iff x).1 hx
    refine (hS₂ S (fun v h => hS (Finset.mem_union_right _ h)) _ (offS_trace ?_)).1
    exact offS_mul_left (adj_intS hx') (offS_mul_left hQ hz)
  · have hQ := hS₁ S (fun v h => hS (Finset.mem_union_left _ h))
    have hx' := (intOff_iff x).1 hx
    refine (hS₂ S (fun v h => hS (Finset.mem_union_right _ h)) _ (offS_trace ?_)).1
    exact offS_mul_right (adj_offS hz) (intS_mul hQ hx')

theorem offS_plc {v : Pl D} (hv : v ∉ S) {t : Fv D.host.F v ⊗[D.host.F] D.host.E}
    (ht : t ∈ intLoc D.host.F D.host.E v) : OffS S (plc D.host.E v t) := by
  refine ⟨fun w => compInf_plc w v t, fun w hw => compFin_plc_ne (by rintro rfl; exact hv hw) t, fun w _ => ?_⟩
  by_cases h : w = v
  · subst h; show compFin _ _ w _ ∈ _; rw [compFin_plc_self]; exact ht
  · show compFin _ _ w _ ∈ _; rw [compFin_plc_ne h]; exact zero_mem _

set_option maxHeartbeats 800000 in

theorem kap_supp (Q : Matrix (Fin r) (Fin r) D.host.E) (hQ : Q.det ≠ 0) (hψ : IsCharAF D.host.F ψ) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ (n : ℕ) (x : Mx D r n), ¬ IntOff S x →
      ∃ z : Mx D r n, OffM S z ∧ kap ψ Q x z ≠ 1 := by
  classical
  obtain ⟨S₁, hS₁⟩ := exists_rat_int Q⁻¹
  obtain ⟨S₂, hS₂⟩ := dual_psi hψ
  refine ⟨S₁ ∪ S₂, fun S hS n x hx => ?_⟩
  have hQi := hS₁ S (fun v h => hS (Finset.mem_union_left _ h))
  simp only [IntOff, not_forall] at hx
  obtain ⟨v, hv, i, j, hij⟩ := hx
  have hv2 : v ∉ S₂ := fun h => hv (hS (Finset.mem_union_right _ h))
  set C : Mx D n r := adj x * rat Q with hCdef
  have hC : ∃ a b, cv D v (C a b) ∉ intLoc D.host.F D.host.E v := by
    by_contra hno
    push Not at hno
    apply hij
    have e1 : adj x = C * rat Q⁻¹ := by
      rw [hCdef, Matrix.mul_assoc, ← rat_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hQ), rat_one, Matrix.mul_one]
    have h2 : cv D v (adj x j i) ∈ intLoc D.host.F D.host.E v := by
      rw [e1, Matrix.mul_apply, map_sum (cv D v)]
      exact sum_mem fun k _ => by rw [RingHom.map_mul]; exact mul_mem (hno j k) (hQi k i v hv)
    have h3 : x i j = cA D (adj x j i) := by
      conv_lhs => rw [← adj_adj x]
      rfl
    rw [h3, LIdemEx.cv_cA]
    exact sigR_mem_intLoc _ h2
  obtain ⟨a, b, hab⟩ := hC
  have ht : ∃ t ∈ intLoc D.host.F D.host.E v,
      psiV D.host.F ψ v (Algebra.trace (Fv D.host.F v) (Fv D.host.F v ⊗[D.host.F] D.host.E) (cv D v (C a b) * t)) ≠ 1 := by
    by_contra h
    push Not at h
    exact hab (hS₂ v hv2 _ h)
  obtain ⟨t, ht, hψt⟩ := ht
  let z : Mx D r n := fun k l => if k = b then (if l = a then plc D.host.E v t else 0) else 0
  have hz : OffM S z := fun k l => by
    simp only [z]
    split_ifs
    · exact offS_plc hv ht
    · exact offS_zero
    · exact offS_zero
  refine ⟨z, hz, ?_⟩
  have htr : Matrix.trace (adj x * (rat Q * z)) = C a b * plc D.host.E v t := by
    rw [← Matrix.mul_assoc, ← hCdef, Matrix.trace, Finset.sum_eq_single a]
    · rw [Matrix.diag_apply, Matrix.mul_apply, Finset.sum_eq_single b]
      · simp [z]
      · intro l _ hl; simp [z, hl]
      · simp
    · intro k _ hk
      rw [Matrix.diag_apply, Matrix.mul_apply]
      exact Finset.sum_eq_zero fun l _ => by simp [z, hk]
    · simp
  unfold kap
  rw [htr, mul_plc, trA_plc]
  exact hψt

theorem ft_good (Q : Matrix (Fin r) (Fin r) D.host.E) (hQ : Q.det ≠ 0) (hψ : IsCharAF D.host.F ψ) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ e, IsIdem S e → ∀ (n : ℕ) (μ : Measure (Mx D r n)), μ.IsAddHaarMeasure →
      ∀ Φ : Mx D r n → ℂ, Good S e Φ →
        Good S e (fun x => ∫ y, Φ y * ψ (trA (Matrix.trace (adj x * (rat Q * y)))) ∂μ) := by
  classical
  obtain ⟨S₁, hS₁⟩ := kap_one Q hψ
  obtain ⟨S₂, hS₂⟩ := kap_supp Q hQ hψ
  refine ⟨S₁ ∪ S₂, fun S hS e he n μ hμ Φ hΦ => ?_⟩
  obtain ⟨i1, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D r n
  have : BorelSpace (Mx D r n) := ⟨rfl⟩
  have : MeasurableAdd (Mx D r n) := inferInstance
  have : μ.IsAddRightInvariant := inferInstance
  have h1 := hS₁ S (fun v h => hS (Finset.mem_union_left _ h)) n
  have h2 := hS₂ S (fun v h => hS (Finset.mem_union_right _ h)) n
  change Good S e (fun x => ∫ y, Φ y * kap ψ Q x y ∂μ)
  refine good_of he (fun x hx => ?_) (fun x z hz => ?_)
  · obtain ⟨z, hz, hk⟩ := h2 x hx
    have e1 : ∫ y, Φ y * kap ψ Q x y ∂μ = (∫ y, Φ y * kap ψ Q x y ∂μ) * kap ψ Q x z := by
      rw [← integral_mul_const, ← integral_add_right_eq_self (fun y => Φ y * kap ψ Q x y) z]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only
      rw [good_shift he hΦ y hz, kap_add_right, mul_assoc]
    have e2 : (∫ y, Φ y * kap ψ Q x y ∂μ) * (kap ψ Q x z - 1) = 0 := by
      rw [mul_sub, mul_one, ← e1, sub_self]
    exact (mul_eq_zero.1 e2).resolve_right (sub_ne_zero.2 hk)
  · refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    by_cases hy : IntOff S y
    · rw [kap_add_left, (h1 y z hy hz).2, mul_one]
    · rw [good_supp hΦ hy, zero_mul, zero_mul]

theorem ft_supp (Q : Matrix (Fin r) (Fin r) D.host.E) (hQ : Q.det ≠ 0) (hψ : IsCharAF D.host.F ψ) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ e, IsIdem S e → ∀ (n : ℕ) (μ : Measure (Mx D r n)), μ.IsAddHaarMeasure →
      ∀ Φ : Mx D r n → ℂ, Good S e Φ → ∀ x : Mx D r n, ¬ IntOff S x →
        ∫ y, Φ y * ψ (trA (Matrix.trace (adj x * (rat Q * y)))) ∂μ = 0 := by
  obtain ⟨S₀, hS₀⟩ := ft_good Q hQ hψ
  exact ⟨S₀, fun S hS e he n μ hμ Φ hΦ x hx => good_supp (hS₀ S hS e he n μ hμ Φ hΦ) hx⟩

end PositivityTheory.Rg.Rsw.L.LFixW

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKH
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Rg.Rsw.L.LGenK

open Matrix

variable {D : D7} {n : ℕ}

theorem cA_invol (x : AE D) : cA D (cA D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => change a ⊗ₜ[D.host.F] D.sp.cm.sig (D.sp.cm.sig e) = _; rw [sig_invol]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem map_neg' {T : Type} [CommRing T] (f : AE D →+* T) (Y : Mx D n n) : (-Y).map f = -(Y.map f) := by
  exact Matrix.map_neg f (map_neg f) Y

theorem map_add' {T : Type} [CommRing T] (f : AE D →+* T) (Y Z : Mx D n n) : (Y + Z).map f = Y.map f + Z.map f := by
  exact Matrix.map_add f (map_add f) Y Z

theorem isM_of (g : G D n) (A u : Mx D n n) (h : mat g = blk4 A 0 0 u) : IsM g := by
  have hunit := mat_unit g
  rw [h] at hunit
  change cj (cA D) (blk4 A 0 0 u) * blk4 0 1 (-1) 0 * blk4 A 0 0 u = blk4 0 1 (-1) 0 at hunit
  have hcol := unit_col (cA D) A 0 0 u (unit_fromBlocks (cA D) A 0 0 u hunit)
  have hAu : cj (cA D) A * u = 1 := by
    have h21 := hcol.2.1
    rwa [mul_zero, sub_zero] at h21
  have hu1 : u * cj (cA D) A = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hAu
  have hcjmul : ∀ M N : Matrix (Fin n) (Fin n) (AE D),
      cj (cA D) (M * N) = cj (cA D) N * cj (cA D) M := by
    intro M N
    show ((M * N).map (cA D))ᵀ = (N.map (cA D))ᵀ * (M.map (cA D))ᵀ
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have hcj1 : cj (cA D) (1 : Matrix (Fin n) (Fin n) (AE D)) = 1 := by
    show ((1 : Matrix (Fin n) (Fin n) (AE D)).map (cA D))ᵀ = 1
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  have hA : A * cj (cA D) u = 1 := by
    have h3 := congrArg (cj (cA D)) hu1
    rwa [hcjmul, cj_cj (cA D) cA_invol, hcj1] at h3
  have hA' : cj (cA D) u * A = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hA
  refine ⟨⟨A, cj (cA D) u, hA, hA'⟩, ?_⟩
  rw [h]
  congr 1
  exact (cj_cj (cA D) cA_invol u).symm

theorem blocks_at {T : Type} [CommRing T] (f : AE D →+* T) {k : G D n} (h : (mat k).map f = 1) :
    (bA (mat k)).map f = 1 ∧ (bB (mat k)).map f = 0 ∧ (bC (mat k)).map f = 0 ∧ (bD (mat k)).map f = 1 := by
  have h2 : blk4 (bA ((mat k).map f)) (bB ((mat k).map f)) (bC ((mat k).map f)) (bD ((mat k).map f)) =
      blk4 1 0 0 1 := by
    rw [block_matrix_of_blocks, block_matrix_one, h]
  exact blockMatrixTwoByTwoFin_injective h2

end PositivityTheory.Rg.Rsw.L.LGenK
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.UnitTriv
section
noncomputable section

set_option synthInstance.maxHeartbeats 400000

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LFixW

set_option maxHeartbeats 1000000 in
open U2 in

theorem unit_triv (D : D7) (χ : (AE D)ˣ →* Circle) (hχ : IsHeckeChar D χ) : ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S →
    ∀ u : (AE D)ˣ, (∀ w, compInf D.host.F D.host.E w (u : AE D) = 1) → (∀ v ∈ S, cv D v (u : AE D) = 1) →
    (∀ v ∉ S, cv D v (u : AE D) ∈ intLoc D.host.F D.host.E v ∧
      cv D v ((u⁻¹ : (AE D)ˣ) : AE D) ∈ intLoc D.host.F D.host.E v) →
    χ u = 1 ∧ absA D u = 1 := by
  obtain ⟨N, hN, hker, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D χ hχ.1
  have hbad : {v : Pl D | ¬ (IsGood D.host.F D.host.E v ∧
      algebraMap D.host.F (Fv D.host.F v) ((N : D.host.F)⁻¹) ∈ v.adicCompletionIntegers D.host.F)}.Finite :=
    Filter.eventually_cofinite.1 ((eventually_good (F := D.host.F) (E := D.host.E)).and
      (eventually_int (F := D.host.F) ((N : D.host.F)⁻¹)))
  refine ⟨hbad.toFinset, fun S hS u hinf hSv hoff => ?_⟩
  have hgood : ∀ v ∉ S, IsGood D.host.F D.host.E v ∧
      algebraMap D.host.F (Fv D.host.F v) ((N : D.host.F)⁻¹) ∈ v.adicCompletionIntegers D.host.F := by
    intro v hv
    by_contra h
    exact hv (hS ((Set.Finite.mem_toFinset hbad).2 h))
  have hinv : ∀ v ∈ S, cv D v ((u⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    intro v hv
    have := congrArg (cv D v) u.inv_mul
    rw [RingHom.map_mul, RingHom.map_one, hSv v hv, mul_one] at this
    exact this
  have hint : ∀ z : AE D, (∀ v ∈ S, cv D v z ∈ intLoc D.host.F D.host.E v) →
      (∀ v ∉ S, cv D v z ∈ intLoc D.host.F D.host.E v) → finPart D z ∈ intAE D := by
    intro z h1 h2
    refine finPart_mem z fun v => ?_
    by_cases hv : v ∈ S
    · exact h1 v hv
    · exact h2 v hv
  have hfu : FinUnit u := ⟨infPart_eq_one hinf,
    hint _ (fun v hv => by rw [hSv v hv]; exact one_mem _) (fun v hv => (hoff v hv).1),
    hint _ (fun v hv => by rw [hinv v hv]; exact one_mem _) (fun v hv => (hoff v hv).2)⟩
  have hy1 : ∀ v ∈ S, cv D v (cN D N * ((u : AE D) - 1)) ∈ intLoc D.host.F D.host.E v := by
    intro v hv
    rw [RingHom.map_mul, RingHom.map_sub, hSv v hv, RingHom.map_one, sub_self, mul_zero]
    exact zero_mem _
  have hy2 : ∀ v ∉ S, cv D v (cN D N * ((u : AE D) - 1)) ∈ intLoc D.host.F D.host.E v := by
    intro v hv
    rw [RingHom.map_mul, RingHom.map_sub, RingHom.map_one]
    have ha : cv D v (cN D N) ∈ intLoc D.host.F D.host.E v := by
      rw [cv_cN]
      exact tmul_one_mem (E := D.host.E) (hgood v hv).2
    have hb : cv D v (u : AE D) - 1 ∈ intLoc D.host.F D.host.E v :=
      (intLoc D.host.F D.host.E v).sub_mem (hoff v hv).1 (intLoc D.host.F D.host.E v).one_mem
    exact (intLoc D.host.F D.host.E v).mul_mem ha hb
  have hy3 : finPart D (u : AE D) - 1 = N • finPart D (cN D N * ((u : AE D) - 1)) := by
    rw [nsmul_eq_mul, ← map_natCast (finPart D) N, ← RingHom.map_mul, ← mul_assoc, natCast_mul_cN hN, one_mul,
      RingHom.map_sub, RingHom.map_one]
  refine ⟨hker u hfu ⟨_, hint _ hy1 hy2, hy3⟩, ?_⟩
  show absE D.host.F D.host.E u = 1
  rw [absE_apply]
  have h1 : ∀ w, absEw D.host.F D.host.E w (unitInf D.host.F D.host.E w u) = 1 := fun w => by
    rw [show unitInf D.host.F D.host.E w u = 1 from Units.ext (hinf w), map_one]
  have h2 : ∀ v, absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v u) = 1 := by
    intro v
    by_cases hv : v ∈ S
    · rw [show unitFin D.host.F D.host.E v u = 1 from Units.ext (hSv v hv), map_one]
    · exact absEv_eq_one (hgood v hv).1 _ (hoff v hv).1 (hoff v hv).2
  rw [Finset.prod_eq_one fun w _ => h1 w, finprod_congr h2, finprod_one, one_mul]

end PositivityTheory.Rg.Rsw.L.LFixW

end
end

