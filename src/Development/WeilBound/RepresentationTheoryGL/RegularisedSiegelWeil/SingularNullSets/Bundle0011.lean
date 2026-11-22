import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0010
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0006
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0007
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterConductorCondition
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0008
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NullSingOfIdemEx

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.BlockMatrixMulUpperUnipotent
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

namespace PositivityTheory.Rg.Rsw.L.LGenK

open Matrix

variable {R : Type} [CommRing R] {n : ℕ}

private theorem blk4_mul_blk4 (A B C E A' B' C' E' : Matrix (Fin n) (Fin n) R) :
    blk4 A B C E * blk4 A' B' C' E' =
      blk4 (A * A' + B * C') (A * B' + B * E') (C * A' + E * C') (C * B' + E * E') := by
  simp only [blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

private theorem cj_one' (s : R →+* R) : cj s (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  unfold cj
  rw [Matrix.map_one _ (map_zero s) (map_one s), Matrix.transpose_one]

theorem fact_alg (s : R →+* R) (a β c u ui : Matrix (Fin n) (Fin n) R) (hu1 : u * ui = 1) (hu2 : ui * u = 1)
    (R2 : c * cj s u = u * cj s c) (C3 : cj s β * u = cj s u * β) :
    cj s (β * ui) = β * ui ∧ cj s (ui * c) = ui * c ∧
      blk4 1 (β * ui) 0 1 * blk4 (a - β * ui * c) 0 0 u * blk4 1 0 (ui * c) 1 = blk4 a β c u := by
  have hcu : cj s ui * cj s u = 1 := by
    rw [← cj_mul, hu1, cj_one']
  have hcu' : cj s u * cj s ui = 1 := by
    rw [← cj_mul, hu2, cj_one']
  have hβ : cj s β = cj s u * β * ui := by
    calc cj s β = cj s β * (u * ui) := by rw [hu1, mul_one]
      _ = cj s u * β * ui := by rw [← mul_assoc, C3]
  have hc : cj s c = ui * c * cj s u := by
    calc cj s c = (ui * u) * cj s c := by rw [hu2, one_mul]
      _ = ui * c * cj s u := by rw [mul_assoc, ← R2, ← mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · rw [cj_mul, hβ, ← mul_assoc, ← mul_assoc, hcu, one_mul]
  · rw [cj_mul, hc, mul_assoc, hcu', mul_one]
  · have e1 : β * ui * u = β := by rw [mul_assoc, hu2, mul_one]
    have e2 : u * (ui * c) = c := by rw [← mul_assoc, hu1, one_mul]
    rw [blk4_mul_blk4, blk4_mul_blk4]
    simp only [mul_zero, zero_mul, add_zero, zero_add, one_mul, mul_one]
    rw [e1, e2, mul_assoc β ui c, sub_add_cancel]

theorem block_matrix_mul_upper_unipotent (a b c d X : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 1 X 0 1 = blk4 a (a * X + b) c (d + c * X) := by
  rw [blk4_mul_blk4]
  simp only [mul_one, mul_zero, add_zero, zero_add]
  rw [add_comm (a * X) b, add_comm (c * X) d]

theorem upper_unipotent_block_inverse (X : Matrix (Fin n) (Fin n) R) : blk4 1 X 0 1 * blk4 1 (-X) 0 1 = 1 := by
  rw [submatrix_fromBlocks_mul]; simp [block_matrix_one]

theorem lower_unipotent_block_inverse (X : Matrix (Fin n) (Fin n) R) : blk4 1 0 X 1 * blk4 1 0 (-X) 1 = 1 := by
  rw [submatrix_fromBlocks_mul]; simp [block_matrix_one]

end PositivityTheory.Rg.Rsw.L.LGenK
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixW_C
section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped TensorProduct
open IsDedekindDomain NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU Filter

namespace PositivityTheory.Rg.Rsw.L.LFixW

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]

theorem trace_map {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (φ : R →ₐ[F] R')
    (z : R ⊗[F] E) :
    Algebra.trace R' (R' ⊗[F] E) (Algebra.TensorProduct.map φ (AlgHom.id F E) z) =
      φ (Algebra.trace R (R ⊗[F] E) z) := by
  classical
  rw [Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis R' (bE F E)),
    Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis R (bE F E)), Matrix.trace, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply]
  have e : Algebra.TensorProduct.map φ (AlgHom.id F E) (z * (1 ⊗ₜ[F] bE F E i)) =
      Algebra.TensorProduct.map φ (AlgHom.id F E) z * (1 ⊗ₜ[F] bE F E i) := by
    rw [map_mul]; simp
  rw [← e, LIdemEx.repr_map']

theorem sgl_self (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) : (singleV F v y) v = y :=
  GlobalTheory.CompanionTheory.PsiCondLoc.single_self v y

theorem sgl_ne (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) {w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) :
    (singleV F v y) w = 0 :=
  GlobalTheory.CompanionTheory.PsiCondLoc.single_ne v y h

theorem sgl_mul (u : Af F) (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) :
    u * singleV F v y = singleV F v (u v * y) :=
  GlobalTheory.CompanionTheory.PsiCondLoc.mul_single u v y

def iV (v : HeightOneSpectrum (𝓞 F)) : Fv F v →ₗ[F] AF F where
  toFun a := pairA F 0 (singleV F v a)
  map_add' a b := by
    refine Prod.ext (by show (0 : Ainf F) = 0 + 0; rw [add_zero]) (Subtype.ext (funext fun w => ?_))
    show (singleV F v (a + b)) w = (singleV F v a) w + (singleV F v b) w
    by_cases h : w = v
    · subst h; rw [sgl_self, sgl_self, sgl_self]
    · rw [sgl_ne v _ h, sgl_ne v _ h, sgl_ne v _ h,
        add_zero]
  map_smul' c a := by
    rw [Algebra.smul_def (A := AF F), RingHom.id_apply]
    refine Prod.ext (by show (0 : Ainf F) = _ * 0; rw [mul_zero]) ?_
    show singleV F v (c • a) = (algebraMap F (Af F) c) * singleV F v a
    rw [sgl_mul, Algebra.smul_def]
    rfl

theorem iV_fst (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) : (iV v a).1 = 0 := rfl

theorem iV_snd (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) : (iV v a).2 = singleV F v a := rfl

variable (E) in

def plc (v : HeightOneSpectrum (𝓞 F)) : Fv F v ⊗[F] E →ₗ[F] AF F ⊗[F] E := TensorProduct.map (iV v) LinearMap.id

theorem plc_tmul (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (e : E) : plc E v (a ⊗ₜ[F] e) = iV v a ⊗ₜ[F] e := rfl

theorem evFin_apply (v : HeightOneSpectrum (𝓞 F)) (y : AF F) : evFin F v y = y.2 v := rfl

theorem evInf_apply (w : InfinitePlace F) (y : AF F) : evInf F w y = y.1 w := rfl

theorem compFin_plc_self (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v ⊗[F] E) : compFin F E v (plc E v t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a e =>
    rw [plc_tmul]
    show evFin F v (iV v a) ⊗ₜ[F] e = _
    rw [evFin_apply, iV_snd, sgl_self]

theorem compFin_plc_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (t : Fv F v ⊗[F] E) :
    compFin F E w (plc E v t) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | tmul a e =>
    rw [plc_tmul]
    show evFin F w (iV v a) ⊗ₜ[F] e = 0
    rw [evFin_apply, iV_snd, sgl_ne v _ h, TensorProduct.zero_tmul]

theorem compInf_plc (w : InfinitePlace F) (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v ⊗[F] E) :
    compInf F E w (plc E v t) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | tmul a e =>
    rw [plc_tmul]
    show evInf F w (iV v a) ⊗ₜ[F] e = 0
    rw [evInf_apply, iV_fst]
    exact TensorProduct.zero_tmul _ _

theorem psi_kernel {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S → ∀ y : AF F, y.1 = 0 → (∀ v ∈ S, y.2 v = 0) →
      (∀ v ∉ S, y.2 v ∈ v.adicCompletionIntegers F) → ψ y = 1 := by
  obtain ⟨α, hα, hk⟩ := GlobalTheory.CompanionTheory.PsiCondLoc.exists_int_kernel hψ
  have hα0 : (α : F) ≠ 0 := by exact_mod_cast hα
  have h1 := Filter.eventually_cofinite.1 (eventually_int (F := F) ((α : F)⁻¹))
  refine ⟨h1.toFinset, fun S hS y hy1 hyS hyI => ?_⟩
  have hu : algebraMap F (Af F) ((α : F)⁻¹) * y.2 ∈ Formalism.UG.intAd F := by
    intro v
    show (algebraMap F (Af F) ((α : F)⁻¹)) v * y.2 v ∈ v.adicCompletionIntegers F
    by_cases hv : v ∈ S
    · rw [hyS v hv, mul_zero]; exact zero_mem _
    · have hv' : v ∉ h1.toFinset := fun h => hv (hS h)
      rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hv'
      exact mul_mem hv' (hyI v hv)
  have e : y = pairA F 0 (algebraMap F (Af F) (α : F) * (algebraMap F (Af F) ((α : F)⁻¹) * y.2)) := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hα0, map_one, one_mul]
    exact Prod.ext hy1 rfl
  rw [e]
  exact hk _ hu

end Gen

section D

open Formalism.BasicNotions Formalism.L2.Theta GlobalTheory.StdUnn

variable {D : D7}

theorem trA_fst (z : AE D) (w : InfinitePlace D.host.F) :
    (trA z).1 w = Algebra.trace w.Completion (w.Completion ⊗[D.host.F] D.host.E) (compInf D.host.F D.host.E w z) := by
  rw [← evInf_apply]
  exact (trace_map (evInf D.host.F w) z).symm

theorem trA_snd (z : AE D) (v : Pl D) :
    (trA z).2 v = Algebra.trace (Fv D.host.F v) (Fv D.host.F v ⊗[D.host.F] D.host.E) (cv D v z) := by
  rw [← evFin_apply]
  exact (trace_map (evFin D.host.F v) z).symm

theorem mul_plc (z : AE D) (v : Pl D) (t : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    z * plc D.host.E v t = plc D.host.E v (cv D v z * t) := by
  refine LIdemEx.ae_ext _ _ (fun w => ?_) (fun w => ?_)
  · rw [map_mul, compInf_plc, compInf_plc, mul_zero]
  · rw [map_mul]
    by_cases h : w = v
    · subst h; rw [compFin_plc_self, compFin_plc_self]
    · rw [compFin_plc_ne h, compFin_plc_ne h, mul_zero]

theorem trA_plc (v : Pl D) (t : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    trA (plc D.host.E v t) =
      pairA D.host.F 0 (singleV D.host.F v (Algebra.trace (Fv D.host.F v) (Fv D.host.F v ⊗[D.host.F] D.host.E) t)) := by
  refine Prod.ext (funext fun w => ?_) (Subtype.ext (funext fun w => ?_))
  · rw [trA_fst, compInf_plc, map_zero]; rfl
  · show (trA (plc D.host.E v t)).2 w = (singleV D.host.F v _) w
    rw [trA_snd]
    by_cases h : w = v
    · subst h; rw [compFin_plc_self, sgl_self]
    · rw [compFin_plc_ne h, map_zero, sgl_ne v _ h]

end D

end PositivityTheory.Rg.Rsw.L.LFixW

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKF
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

section Blocks

variable {R : Type} [CommRing R] {n : ℕ}

theorem blocks_one : bA (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 1 ∧ bB (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 0 ∧
    bC (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 0 ∧ bD (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 1 := by
  have h : (1 : Matrix (Fin (n + n)) (Fin (n + n)) R).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks 1 0 0 1 := by
    rw [Matrix.submatrix_one_equiv, Matrix.fromBlocks_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ((1 : Matrix (Fin (n + n)) (Fin (n + n)) R).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁ = 1
    rw [h, Matrix.toBlocks_fromBlocks₁₁]
  · show ((1 : Matrix (Fin (n + n)) (Fin (n + n)) R).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂ = 0
    rw [h, Matrix.toBlocks_fromBlocks₁₂]
  · show ((1 : Matrix (Fin (n + n)) (Fin (n + n)) R).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0
    rw [h, Matrix.toBlocks_fromBlocks₂₁]
  · show ((1 : Matrix (Fin (n + n)) (Fin (n + n)) R).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂ = 1
    rw [h, Matrix.toBlocks_fromBlocks₂₂]

theorem bC_map {S : Type} [CommRing S] (f : R →+* S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : bC (M.map f) = (bC M).map f := rfl
theorem bD_map {S : Type} [CommRing S] (f : R →+* S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : bD (M.map f) = (bD M).map f := rfl

theorem weyl_block_matrix_map {S : Type} [CommRing S] (f : R →+* S) :
    (blk4 (0 : Matrix (Fin n) (Fin n) R) 1 (-1) 0).map f = blk4 0 1 (-1) 0 := by
  rw [block_matrix_map]
  have h0 : (0 : Matrix (Fin n) (Fin n) R).map f = 0 := Matrix.map_zero _ (map_zero f)
  have h1 : (1 : Matrix (Fin n) (Fin n) R).map f = 1 := Matrix.map_one _ (map_zero f) (map_one f)
  have hn : (-1 : Matrix (Fin n) (Fin n) R).map f = -1 := by
    rw [Matrix.map_neg _ (fun a => map_neg f a), h1]
  rw [h0, h1, hn]

end Blocks

variable {D : D7} {n : ℕ}

theorem sig_invol (x : D.host.E) : D.sp.cm.sig (D.sp.cm.sig x) = x := by
  exact star_star x

theorem sig_ne : D.sp.cm.sig ≠ AlgHom.id D.host.F D.host.E := by
  intro h
  have h1 : ∀ a : D.host.E, star a = a := fun a => by
    have := DFunLike.congr_fun h a
    exact this
  have htop : (⊥ : Subalgebra D.host.F D.host.E) = ⊤ := by
    refine eq_top_iff.mpr fun a _ => ?_
    rw [Algebra.mem_bot]
    obtain ⟨r, hr⟩ := (D.sp.cm.fixed a).mp (h1 a)
    exact ⟨r, hr⟩
  have h2 := Subalgebra.bot_eq_top_iff_finrank_eq_one.mp htop
  rw [D.sp.cm.deg2] at h2
  exact absurd h2 (by norm_num)

private theorem cv_cA_lemma (v : Pl D) (x : AE D) :
    cv D v (cA D x) = sigR (Fv D.host.F v) D.sp.cm.sig (cv D v x) := by
  have key : ((Algebra.TensorProduct.map (GlobalTheory.AdelicU.evFin D.host.F v) (AlgHom.id D.host.F D.host.E)).comp
      (Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig)) =
      (Algebra.TensorProduct.map (AlgHom.id D.host.F (Fv D.host.F v)) D.sp.cm.sig).comp
        (Algebra.TensorProduct.map (GlobalTheory.AdelicU.evFin D.host.F v) (AlgHom.id D.host.F D.host.E)) := by
    rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp]
    simp only [AlgHom.id_comp, AlgHom.comp_id]
  exact DFunLike.congr_fun key x

theorem unit_loc (v : Pl D) (g : G D n) :
    cj (sigR (Fv D.host.F v) D.sp.cm.sig) (fromBlocks (bA ((mat g).map (cv D v))) (bB ((mat g).map (cv D v)))
        (bC ((mat g).map (cv D v))) (bD ((mat g).map (cv D v)))) * fromBlocks 0 1 (-1) 0 *
      fromBlocks (bA ((mat g).map (cv D v))) (bB ((mat g).map (cv D v))) (bC ((mat g).map (cv D v)))
        (bD ((mat g).map (cv D v))) = fromBlocks 0 1 (-1) 0 := by
  have hcj : (cj (cA D) (mat g)).map (cv D v) =
      cj (sigR (Fv D.host.F v) D.sp.cm.sig) ((mat g).map (cv D v)) := by
    ext i j
    exact cv_cA_lemma v (mat g j i)
  have hJ : (Jm D n).map (cv D v) = blk4 0 1 (-1) 0 := weyl_block_matrix_map (cv D v)
  have h2 := congrArg (fun N => N.map (cv D v)) (mat_unit g)
  simp only [Matrix.map_mul] at h2
  rw [hcj, hJ] at h2
  apply unit_fromBlocks
  rw [block_matrix_of_blocks]
  exact h2

theorem det_map_u {T : Type} [CommRing T] (f : AE D →+* T) (M : Mx D (n + n) (n + n)) (X : Mx D n n) :
    f (bD M + bC M * X).det = (bD (M.map f) + bC (M.map f) * X.map f).det := by
  rw [RingHom.map_det, RingHom.map_add, RingHom.map_mul, bD_map, bC_map]
  rfl

theorem exists_X {S : Finset (Pl D)} (hS2 : ∀ v ∉ S, (2 : 𝓞 D.host.F) ∉ v.asIdeal) {k : G D n} (hk : k ∈ KOff D n S) :
    ∃ X : Mx D n n, cj (cA D) X = X ∧ X.map (infPart D) = 0 ∧ (∀ v ∈ S, X.map (cv D v) = 0) ∧
      (∀ v ∉ S, ∀ i j, cv D v (X i j) ∈ intLoc D.host.F D.host.E v) ∧
      (∀ v, ∃ z ∈ intLoc D.host.F D.host.E v, cv D v (bD (mat k) + bC (mat k) * X).det * z = 1) ∧
      IsUnit (bD (mat k) + bC (mat k) * X).det := by
  classical
  obtain ⟨hinf, hSv, hint⟩ := KOff_props hk
  have hloc : ∀ v, v ∉ S → ∃ x : Matrix (Fin n) (Fin n) (Fv D.host.F v ⊗[D.host.F] D.host.E),
      (∀ i j, x i j ∈ intLoc D.host.F D.host.E v) ∧ cj (sigR (Fv D.host.F v) D.sp.cm.sig) x = x ∧
      ∃ z ∈ intLoc D.host.F D.host.E v,
        (bD ((mat k).map (cv D v)) + bC ((mat k).map (cv D v)) * x).det * z = 1 := fun v hv =>
    local_choice v D.sp.cm.sig sig_invol sig_ne D.sp.cm.deg2 (hS2 v hv) _ _ _ _
      (fun i j => hint v hv _ _) (fun i j => hint v hv _ _) (fun i j => hint v hv _ _) (fun i j => hint v hv _ _)
      (unit_loc v k)
  choose x hx using hloc
  let b : ∀ v : Pl D, Matrix (Fin n) (Fin n) (Fv D.host.F v ⊗[D.host.F] D.host.E) :=
    fun v => if hv : v ∈ S then 0 else x v hv
  have hb : ∀ v i j, b v i j ∈ intLoc D.host.F D.host.E v := by
    intro v i j
    by_cases hv : v ∈ S
    · simp only [b, dif_pos hv]; exact zero_mem _
    · simp only [b, dif_neg hv]; exact (hx v hv).1 i j
  obtain ⟨X, hXc, hXi⟩ := glue_mat D b hb
  have hXv : ∀ v (hv : v ∉ S), X.map (cv D v) = x v hv := by
    intro v hv; ext i j; rw [Matrix.map_apply, hXc]; simp only [b, dif_neg hv]
  have hXinf : X.map (infPart D) = 0 := by ext i j; exact hXi i j
  have hz : ∀ v, ∃ z ∈ intLoc D.host.F D.host.E v, cv D v (bD (mat k) + bC (mat k) * X).det * z = 1 := by
    intro v
    rw [det_map_u]
    by_cases hv : v ∈ S
    · refine ⟨1, one_mem _, ?_⟩
      rw [hSv v hv, blocks_one.2.2.1, blocks_one.2.2.2]; simp
    · rw [hXv v hv]; exact (hx v hv).2.2
  refine ⟨X, ?_, hXinf, fun v hv => ?_, fun v hv i j => ?_, hz, ?_⟩
  · ext i j
    apply ext_comp
    · intro v
      rw [cj_apply, cv_cA, hXc, hXc]
      by_cases hv : v ∈ S
      · simp only [b, dif_pos hv, Matrix.zero_apply, map_zero]
      · simp only [b, dif_neg hv]
        have := congrFun (congrFun (hx v hv).2.1 i) j
        rw [cj_apply] at this
        exact this
    · rw [cj_apply, infPart_cA, hXi, hXi, map_zero]
  · ext i j; rw [Matrix.map_apply, hXc]; simp only [b, dif_pos hv, Matrix.zero_apply]
  · rw [hXc]; exact hb v i j
  · refine isUnit_of_comp D _ hz ?_
    rw [det_map_u, hinf, hXinf, blocks_one.2.2.1, blocks_one.2.2.2]; simp

end PositivityTheory.Rg.Rsw.L.LGenK
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LNullSing
section
namespace PositivityTheory.Rg.Rsw.L

theorem nullSing : IdemEx → NullSing := GlobalTheory.CompanionTheory.NullFr.nullSing_of_idemEx

end PositivityTheory.Rg.Rsw.L
end

