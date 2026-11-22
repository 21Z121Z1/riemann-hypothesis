import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0160
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0317
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolarPartIdentity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0145

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCutIdA
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

namespace PositivityTheory.Rg.Rsw.L.LCutId

open GlobalTheory.StdUnn.Model

variable {D : D7} {n : ℕ}

theorem repr_map' {F E R R' ι : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (φ : R →ₐ[F] R') (b : Module.Basis ι F E) (z : R ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) k =
      φ ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]

theorem ae_ext (z z' : AE D) (hi : ∀ w, compInf D.host.F D.host.E w z = compInf D.host.F D.host.E w z')
    (hf : ∀ v, cv D v z = cv D v z') : z = z' := by
  let b := Module.Basis.ofVectorSpace D.host.F D.host.E
  apply (Algebra.TensorProduct.basis (AF D.host.F) b).repr.injective
  refine Finsupp.ext fun k => Prod.ext ?_ ?_
  · funext w
    have h1 := repr_map' (evInf D.host.F w) b z k
    have h2 := repr_map' (evInf D.host.F w) b z' k
    have h : Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) z =
        Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) z' := hi w
    rw [h, h2] at h1
    exact h1.symm
  · refine FiniteAdeleRing.ext _ fun v => ?_
    have h1 := repr_map' (evFin D.host.F v) b z k
    have h2 := repr_map' (evFin D.host.F v) b z' k
    have h : Algebra.TensorProduct.map (evFin D.host.F v) (AlgHom.id D.host.F D.host.E) z =
        Algebra.TensorProduct.map (evFin D.host.F v) (AlgHom.id D.host.F D.host.E) z' := hf v
    rw [h, h2] at h1
    exact h1.symm

theorem fst_zero (z : AE D) (h : ∀ w, compInf D.host.F D.host.E w z = 0) :
    Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) z = 0 := by
  let b := Module.Basis.ofVectorSpace D.host.F D.host.E
  have hk : ∀ k, ((Algebra.TensorProduct.basis (AF D.host.F) b).repr z k).1 = 0 := fun k => by
    funext w
    have h1 := repr_map' (evInf D.host.F w) b z k
    have h2 : Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) z = 0 := h w
    rw [h2, LinearEquiv.map_zero, Finsupp.zero_apply] at h1
    exact h1.symm
  apply (Algebra.TensorProduct.basis (Ainf D.host.F) b).repr.injective
  refine Finsupp.ext fun k => ?_
  rw [repr_map', LinearEquiv.map_zero, Finsupp.zero_apply]
  exact hk k

theorem block_matrix_map_ringHom {R S : Type} [Semiring R] [Semiring S] (φ : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map φ = blk4 (a.map φ) (b.map φ) (c.map φ) (d.map φ) := by
  ext i j
  simp only [blk4, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

theorem unipotent_block_mem_subring {S : Type} [Ring S] (T : Subring S) (Y : Matrix (Fin n) (Fin n) S) (hY : ∀ i j, Y i j ∈ T) (i j : Fin (n + n)) :
    blk4 1 Y 0 1 i j ∈ T := by
  simp only [blk4, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j
  · rw [Matrix.fromBlocks_apply₁₁, Matrix.one_apply]; split_ifs; exacts [T.one_mem, T.zero_mem]
  · rw [Matrix.fromBlocks_apply₁₂]; exact hY i j
  · rw [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]; exact T.zero_mem
  · rw [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]; split_ifs; exacts [T.one_mem, T.zero_mem]

theorem mat_nb_map {nb : hermA D n → G D n} (hnb : IsNMap nb) {S : Type} [CommRing S] (φ : AE D →+* S) (y : hermA D n) :
    (mat (nb y)).map φ = blk4 1 (y.1.map φ) 0 1 := by
  rw [hnb y, block_matrix_map_ringHom, Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.map_zero _ (map_zero φ)]

theorem mat_nb_map_one {nb : hermA D n → G D n} (hnb : IsNMap nb) {S : Type} [CommRing S] (φ : AE D →+* S) (y : hermA D n)
    (h : ∀ i j, φ (y.1 i j) = 0) : (mat (nb y)).map φ = 1 := by
  rw [mat_nb_map hnb, show y.1.map φ = 0 from Matrix.ext fun i j => h i j, block_matrix_one]

theorem map_comm {m : ℕ} {S : Type} [CommRing S] (φ : AE D →+* S) (A B : Mx D m m) (h : A.map φ = 1 ∨ B.map φ = 1) :
    (A * B).map φ = (B * A).map φ := by
  rw [Matrix.map_mul, Matrix.map_mul]
  rcases h with h | h <;> rw [h, one_mul, mul_one]

theorem nb_comm {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D} {y : hermA D n}
    (hi : ∀ w i j, compInf D.host.F D.host.E w (y.1 i j) = 0) (ho : ∀ v' ≠ v, ∀ i j, cv D v' (y.1 i j) = 0)
    {g : G D n} (hg : proj D.sp.cm.sig (Jst D n) v g = 1) : nb y * g = g * nb y := by
  apply GlobalTheory.CompanionTheory.FourierN.mat_injective
  show mat (nb y) * mat g = mat g * mat (nb y)
  have hgv : (mat g).map (cv D v) = 1 := by
    have e := congrArg (fun k => (GlobalTheory.AdelicU.matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n) k).1) hg
    simp only [map_one, Units.val_one] at e
    exact e
  have key : ∀ {S : Type} [CommRing S] (φ : AE D →+* S), (mat (nb y)).map φ = 1 ∨ (mat g).map φ = 1 →
      ∀ i j, φ ((mat (nb y) * mat g) i j) = φ ((mat g * mat (nb y)) i j) := by
    intro S _ φ h i j
    have e := map_comm φ (mat (nb y)) (mat g) h
    exact congrFun (congrFun e i) j
  ext i j
  refine ae_ext _ _ (fun w => key _ (Or.inl (mat_nb_map_one hnb _ y fun a b => hi w a b)) i j) (fun v' => ?_)
  by_cases hv : v' = v
  · subst hv
    exact key _ (Or.inr hgv) i j
  · exact key _ (Or.inl (mat_nb_map_one hnb _ y fun a b => ho v' hv a b)) i j

theorem stab_of_int (v : Pl D) (k : GLoc D.sp.cm.sig (Jst D n) v)
    (hM : ∀ i j, (GlobalTheory.AdelicU.matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n) k).1 i j ∈ intLoc D.host.F D.host.E v)
    (hM' : ∀ i j, ((GlobalTheory.AdelicU.matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n) k)⁻¹).1 i j ∈ intLoc D.host.F D.host.E v) :
    k ∈ stabLoc D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) v := by
  set M := GlobalTheory.AdelicU.matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n) k
  have hint : ∀ (N : Matrix (Fin (n + n)) (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)),
      (∀ i j, N i j ∈ intLoc D.host.F D.host.E v) → ∀ z : Fin (n + n) → Fv D.host.F v ⊗[D.host.F] D.host.E,
      (∀ i, z i ∈ intLoc D.host.F D.host.E v) → ∀ i, (N *ᵥ z) i ∈ intLoc D.host.F D.host.E v :=
    fun N hN z hz i => by
      simp only [Matrix.mulVec, dotProduct]
      exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hN i j) (hz j)
  refine GlobalTheory.AdelicU.mem_stabLoc.2 fun z => ?_
  simp only [GlobalTheory.AdelicU.mem_latLoc_stdLattice]
  refine ⟨fun hz => hint _ hM z hz, fun hz => ?_⟩
  have e : (M⁻¹).1 *ᵥ (M.1 *ᵥ z) = z := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [← e]
  exact hint _ hM' _ hz

set_option maxHeartbeats 800000 in

theorem nb_mem_KAt {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D} {y : hermA D n} (hy : IntAt v y) :
    nb y ∈ KAt D n v := by
  obtain ⟨hi, ho, hint⟩ := hy
  have hcv : ∀ (v' : Pl D) i j, cv D v' (y.1 i j) ∈ intLoc D.host.F D.host.E v' := by
    intro v' i j
    by_cases hv : v' = v
    · subst hv; exact hint i j
    · rw [ho v' hv i j]; exact zero_mem _
  have hinv : (nb y)⁻¹ = nb (-y) := by
    rw [inv_eq_iff_mul_eq_one, ← GlobalTheory.CompanionTheory.FourierN.nb_add hnb, add_neg_cancel, GlobalTheory.CompanionTheory.FourierN.nb_zero hnb]
  have hstab : ∀ v' : Pl D, proj D.sp.cm.sig (Jst D n) v' (nb y) ∈
      stabLoc D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) v' := by
    intro v'
    refine stab_of_int v' _ (fun i j => ?_) (fun i j => ?_)
    · change ((mat (nb y)).map (cv D v')) i j ∈ _
      rw [mat_nb_map hnb]
      exact unipotent_block_mem_subring _ _ (fun a b => hcv v' a b) i j
    · rw [← map_inv, ← map_inv, hinv]
      change ((mat (nb (-y))).map (cv D v')) i j ∈ _
      rw [mat_nb_map hnb]
      refine unipotent_block_mem_subring _ _ (fun a b => ?_) i j
      show cv D v' ((-y).1 a b) ∈ _
      rw [show (-y).1 a b = -(y.1 a b) from rfl, RingHom.map_neg]
      exact neg_mem (hcv v' a b)
  have harch : ∀ w, projArch D.sp.cm.sig (Jst D n) w (nb y) = 1 := fun w =>
    Subtype.ext (Units.ext (mat_nb_map_one hnb _ y fun a b => hi w a b))
  have hoff : ∀ v' ≠ v, proj D.sp.cm.sig (Jst D n) v' (nb y) = 1 := fun v' hv =>
    Subtype.ext (Units.ext (mat_nb_map_one hnb _ y fun a b => ho v' hv a b))
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · show nb y ∈ levelAll D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) 1
    refine Subgroup.mem_inf.2 ⟨mem_levelOpen.2 hstab, Subgroup.mem_iInf.2 fun w => ?_⟩
    rw [Subgroup.mem_comap, harch w]
    exact one_mem _
  · refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · show nb y ∈ MonoidHom.ker _
      rw [MonoidHom.mem_ker]
      have e := mat_nb_map_one hnb (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom y
        fun a b => fst_zero _ fun w => hi w a b
      apply Units.ext
      rw [MonoidHom.comp_apply, Formalism.UG.bc, Units.coe_map, Units.val_one]
      exact e
    · refine Subgroup.mem_iInf.2 fun v' => Subgroup.mem_iInf.2 fun hv' => ?_
      rw [MonoidHom.mem_ker]
      exact hoff v' fun h => hv' (Finset.mem_singleton.2 h)

end PositivityTheory.Rg.Rsw.L.LCutId

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCutLowA
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

namespace PositivityTheory.Rg.Rsw.L.LCutLow

variable {D : D7} {n : ℕ}

theorem matHom_proj_val (v : Pl D) (g : G D n) :
    (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D n) (proj D.sp.cm.sig (Jst D n) v g)).1 = (mat g).map (cv D v) := by
  rw [GlobalTheory.AdelicU.matHom_proj]; rfl

theorem matHom_projArch_val (w : InfinitePlace D.host.F) (g : G D n) :
    (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D n) (projArch D.sp.cm.sig (Jst D n) w g)).1 =
      (mat g).map (compInf D.host.F D.host.E w) := by
  rw [GlobalTheory.AdelicU.matHom_projArch]; rfl

theorem block_matrix_diagonal_one_eq_one {R : Type} [CommRing R] : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  unfold blk4
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem block_matrix_entry_property {R : Type} [CommRing R] (S : Subring R) {a b c d : Matrix (Fin n) (Fin n) R}
    (ha : ∀ i j, a i j ∈ S) (hb : ∀ i j, b i j ∈ S) (hc : ∀ i j, c i j ∈ S) (hd : ∀ i j, d i j ∈ S) (i j : Fin (n + n)) :
    blk4 a b c d i j ∈ S := by
  unfold blk4
  simp only [Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i' | i' <;> rcases finSumFinEquiv.symm j with j' | j' <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  exacts [ha _ _, hb _ _, hc _ _, hd _ _]

theorem map_mat_nb {nb : hermA D n → G D n} (hnb : IsNMap nb) {S : Type} [CommRing S] (f : AE D →+* S) (x : hermA D n) :
    (mat (nb x)).map f = blk4 1 (x.1.map f) 0 1 := by
  rw [hnb x, GlobalTheory.CompanionTheory.FourierN.blk4_map_alt, Matrix.map_one _ (map_zero f) (map_one f), Matrix.map_zero _ (map_zero f)]

theorem proj_nb_eq_one {nb : hermA D n → G D n} (hnb : IsNMap nb) (v : Pl D) {x : hermA D n}
    (hx : ∀ i j, cv D v (x.1 i j) = 0) : proj D.sp.cm.sig (Jst D n) v (nb x) = 1 := by
  refine GlobalTheory.AdelicU.matHom_injective _ _ _ (Units.ext ?_)
  rw [map_one, Units.val_one, matHom_proj_val, map_mat_nb hnb]
  have : x.1.map (cv D v) = 0 := Matrix.ext fun i j => hx i j
  rw [this, block_matrix_diagonal_one_eq_one]

theorem projArch_nb_eq_one {nb : hermA D n → G D n} (hnb : IsNMap nb) (w : InfinitePlace D.host.F) {x : hermA D n}
    (hx : ∀ i j, compInf D.host.F D.host.E w (x.1 i j) = 0) : projArch D.sp.cm.sig (Jst D n) w (nb x) = 1 := by
  refine GlobalTheory.AdelicU.matHom_injective _ _ _ (Units.ext ?_)
  rw [map_one, Units.val_one, matHom_projArch_val, map_mat_nb hnb]
  have : x.1.map (compInf D.host.F D.host.E w) = 0 := Matrix.ext fun i j => hx i j
  rw [this, block_matrix_diagonal_one_eq_one]

theorem nb_mem_atPts {nb : hermA D n → G D n} (hnb : IsNMap nb) (v : Pl D) {x : hermA D n}
    (hinf : ∀ w i j, compInf D.host.F D.host.E w (x.1 i j) = 0) (hoff : ∀ v' ≠ v, ∀ i j, cv D v' (x.1 i j) = 0) :
    nb x ∈ atPts D.sp.cm.sig (Jst D n) {v} :=
  GlobalTheory.AdelicU.mem_atPts.2 ⟨GlobalTheory.AdelicU.mem_finPts_iff_forall.2 fun w => projArch_nb_eq_one hnb w (hinf w),
    fun v' hv' => proj_nb_eq_one hnb v' (hoff v' (by simpa using hv'))⟩

theorem nb_neg {nb : hermA D n → G D n} (hnb : IsNMap nb) (x : hermA D n) : nb (-x) = (nb x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← GlobalTheory.CompanionTheory.FourierN.nb_add hnb, neg_add_cancel, GlobalTheory.CompanionTheory.FourierN.nb_zero hnb])

theorem proj_nb_entry {nb : hermA D n → G D n} (hnb : IsNMap nb) (v : Pl D) {y : hermA D n}
    (hy : ∀ i j, cv D v (y.1 i j) ∈ intLoc D.host.F D.host.E v) (i j : Fin (n + n)) :
    (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D n) (proj D.sp.cm.sig (Jst D n) v (nb y))).1 i j ∈ intLoc D.host.F D.host.E v := by
  rw [matHom_proj_val, map_mat_nb hnb]
  refine block_matrix_entry_property _ (fun a b => ?_) (fun a b => hy a b) (fun a b => ?_) (fun a b => ?_) i j
  · rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  · exact zero_mem _
  · rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem proj_nb_mem_stabLoc {nb : hermA D n → G D n} (hnb : IsNMap nb) (v : Pl D) {x : hermA D n}
    (hx : ∀ i j, cv D v (x.1 i j) ∈ intLoc D.host.F D.host.E v) :
    proj D.sp.cm.sig (Jst D n) v (nb x) ∈ stabLoc D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) v := by
  refine GlobalTheory.AdelicU.mem_stabLoc_stdLattice_iff.2 ⟨proj_nb_entry hnb v hx, ?_⟩
  have e : (proj D.sp.cm.sig (Jst D n) v (nb x))⁻¹ = proj D.sp.cm.sig (Jst D n) v (nb (-x)) := by
    rw [nb_neg hnb, map_inv]
  rw [e]
  refine proj_nb_entry hnb v fun i j => ?_
  have h1 : cv D v ((-x).1 i j) = -cv D v (x.1 i j) := RingHom.map_neg (cv D v) (x.1 i j)
  rw [h1]
  exact neg_mem (hx i j)

theorem mem_KAt_of {v : Pl D} {y : G D n}
    (h1 : y ∈ levelOpen D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n))) (h2 : y ∈ atPts D.sp.cm.sig (Jst D n) {v}) :
    y ∈ KAt D n v := by
  refine Subgroup.mem_inf.2 ⟨?_, h2⟩
  show y ∈ levelAll D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) 1
  refine GlobalTheory.AdelicU.mem_levelAll.2 ⟨GlobalTheory.AdelicU.mem_levelOpen.1 h1, fun w => ?_⟩
  rw [GlobalTheory.AdelicU.mem_finPts_iff_forall.1 (GlobalTheory.AdelicU.mem_atPts.1 h2).1 w]
  exact one_mem _

theorem nb_mem_KAt {nb : hermA D n → G D n} (hnb : IsNMap nb) (v : Pl D) {x : hermA D n} (hx : IntAt v x) :
    nb x ∈ KAt D n v := by
  refine mem_KAt_of (GlobalTheory.AdelicU.mem_levelOpen.2 fun v' => ?_) (nb_mem_atPts hnb v hx.1 hx.2.1)
  by_cases h : v' = v
  · subst h; exact proj_nb_mem_stabLoc hnb _ hx.2.2
  · rw [proj_nb_eq_one hnb v' (hx.2.1 v' h)]; exact one_mem _

theorem commute_of_atPts {v : Pl D} {x g : G D n} (hx : x ∈ atPts D.sp.cm.sig (Jst D n) {v})
    (hg : proj D.sp.cm.sig (Jst D n) v g = 1) : x * g = g * x :=
  (GlobalTheory.AdelicU.commute_atPts_awayPts _ _ hx (GlobalTheory.AdelicU.mem_awayPts.2 fun u hu => by
    rw [Finset.mem_singleton.1 hu]; exact hg)).eq

def lev (nb : hermA D n → G D n) (s : Finset (hermA D n)) : Subgroup (G D n) :=
  ⨅ x : s, (levelOpen D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n))).comap (MulAut.conj (nb x.1)⁻¹).toMonoidHom

theorem isOpen_lev (nb : hermA D n → G D n) (s : Finset (hermA D n)) : IsOpen (lev nb s : Set (G D n)) := by
  have : Submodule.IsLattice D.host.E (stdLattice D.host.E (n + n)) := GlobalTheory.AdelicU.isLattice_stdLattice
  rw [lev, Subgroup.coe_iInf]
  refine isOpen_iInter_of_finite fun x => ?_
  rw [Subgroup.coe_comap]
  exact (GlobalTheory.AdelicU.isOpen_levelOpen _ _ _).preimage ((continuous_mul_const _).comp (continuous_const_mul _))

theorem conj_mem_KAt {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D} (C : Cut D n v) {k : G D n}
    (hk : k ∈ lev nb C.s) (hkv : k ∈ atPts D.sp.cm.sig (Jst D n) {v}) {x : hermA D n} (hx : x ∈ C.s) :
    (nb x)⁻¹ * k * nb x ∈ KAt D n v := by
  have h1 := Subgroup.mem_iInf.1 hk ⟨x, hx⟩
  rw [Subgroup.mem_comap] at h1
  have hat := nb_mem_atPts hnb v (C.inf x hx) (C.off x hx)
  refine mem_KAt_of ?_ (mul_mem (mul_mem (inv_mem hat) hkv) hat)
  simpa [MulAut.conj_apply] using h1

end PositivityTheory.Rg.Rsw.L.LCutLow

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFourierPt
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

namespace PositivityTheory.Rg.Rsw.L.LFourierPt

variable {D : D7} {n : ℕ}

theorem conj_pch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (a : Matrix (Fin n) (Fin n) D.host.E)
    (x : Mx D n n) : conj (pch ψ x (rat a)) = ψ (-GlobalTheory.CompanionTheory.FourierN.pr a x) := by
  have e : pch ψ x (rat a) = ψ (GlobalTheory.CompanionTheory.FourierN.pr a x) := by
    rw [pch, GlobalTheory.CompanionTheory.FourierN.pr]
    congr 2
    exact Matrix.trace_mul_comm _ _
  rw [e, AddChar.map_neg_eq_inv]
  have hn : ‖ψ (GlobalTheory.CompanionTheory.FourierN.pr a x)‖ = 1 := hψ.2.1 _
  have hne : ψ (GlobalTheory.CompanionTheory.FourierN.pr a x) ≠ 0 := by
    intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
  simp

end PositivityTheory.Rg.Rsw.L.LFourierPt

namespace PositivityTheory.Rg.Rsw.L

open LFourierPt

set_option synthInstance.maxHeartbeats 400000 in
theorem fourierPt : FourierPt := by
  intro D n ψ hψ lam 𝓖 hC f hf hper hco
  obtain ⟨hlam, hFD, -⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D n n
  have : BorelSpace (Mx D n n) := ⟨rfl⟩
  have : BorelSpace (hermA D n) := Subtype.borelSpace _
  have : SecondCountableTopology (hermA D n) := TopologicalSpace.Subtype.secondCountableTopology _
  have : LocallyCompactSpace (hermA D n) :=
    GlobalTheory.CompanionTheory.FourierN.isClosed_hermA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : DiscreteTopology (ratHerm D n) := GlobalTheory.CompanionTheory.FourierN.discrete_ratHerm
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := n)
  exact GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (hermA D n) (ratHerm D n) K hK hcov
    (GlobalTheory.CompanionTheory.FourierN.hermSub D n) (fun a x => ψ (-GlobalTheory.CompanionTheory.FourierN.pr a.1 x.1))
    (fun a => hψ.1.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_pr a.1).neg.comp continuous_subtype_val))
    (fun a x y => by
      show ψ (-GlobalTheory.CompanionTheory.FourierN.pr a.1 (x.1 + y.1)) = _
      rw [GlobalTheory.CompanionTheory.FourierN.pr_add_right, neg_add, AddChar.map_add_eq_mul])
    (fun a b x => by
      show ψ (-GlobalTheory.CompanionTheory.FourierN.pr (a.1 + b.1) x.1) = _
      rw [GlobalTheory.CompanionTheory.FourierN.pr_add_left, neg_add, AddChar.map_add_eq_mul])
    (fun x => by
      show ψ (-GlobalTheory.CompanionTheory.FourierN.pr 0 x.1) = 1
      rw [GlobalTheory.CompanionTheory.FourierN.pr_zero_left, neg_zero, AddChar.map_zero_eq_one])
    (fun a x => hψ.2.1 _)
    (fun x => ⟨fun h => GlobalTheory.CompanionTheory.FourierN.rat_ker hψ x (fun a ha => h ⟨a, ha⟩),
      fun hx a => GlobalTheory.CompanionTheory.FourierN.ker_of_rat hψ x hx a.1⟩)
    lam 𝓖 hlam hFD f hf hper
    (fun a => by
      have h := hco ⟨a.1, a.2⟩
      refine (integral_congr_ae (.of_forall fun x => ?_)).trans h
      show ψ (-GlobalTheory.CompanionTheory.FourierN.pr a.1 x.1) * f x = f x * conj (pch ψ x.1 (rat a.1))
      rw [conj_pch hψ, mul_comm])

end PositivityTheory.Rg.Rsw.L

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LResCoreA
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

namespace PositivityTheory.Rg.Rsw.L.LResCore

open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

variable {D : D7} {n : ℕ}

theorem kAt_le_kOff {v : Pl D} {S : Finset (Pl D)} (hv : v ∉ S) : KAt D n v ≤ KOff D n S := by
  intro k hk
  obtain ⟨hK, hA⟩ := Subgroup.mem_inf.1 hk
  rw [mem_atPts] at hA
  rw [KOff, mem_levelOff]
  refine ⟨hA.1, fun w hw => hA.2 w ?_, fun w _ => ?_⟩
  · rw [Finset.mem_singleton]
    rintro rfl
    exact hv hw
  · by_cases hwv : w = v
    · subst hwv
      have h1 : k ∈ levelOpen D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) := hK.1
      exact Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 h1 w)
    · rw [hA.2 w (by rwa [Finset.mem_singleton])]
      exact one_mem _

theorem isCompact_kAt (v : Pl D) : IsCompact (KAt D n v : Set (G D n)) := by
  have : Submodule.IsLattice D.host.E (stdLattice D.host.E (n + n)) := isLattice_stdLattice
  have hK : IsCompact (K D n : Set (G D n)) := isCompact_levelAll (isCMExt_host D) _ _ _
  have e : (atPts D.sp.cm.sig (Jst D n) {v} : Set (G D n)) = (finPts D.sp.cm.sig (Jst D n) : Set (G D n)) ∩
      ⋂ w, ⋂ (_ : w ∉ ({v} : Finset (Pl D))), (proj D.sp.cm.sig (Jst D n) w) ⁻¹' {1} := by
    ext k
    simp only [SetLike.mem_coe, mem_atPts, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
  have hA : IsClosed (atPts D.sp.cm.sig (Jst D n) {v} : Set (G D n)) := by
    rw [e]
    exact (isClosed_finPts _ _).inter (isClosed_iInter fun w => isClosed_iInter fun _ =>
      isClosed_singleton.preimage (continuous_proj _ _ w))
  have e2 : (KAt D n v : Set (G D n)) = (K D n : Set (G D n)) ∩ (atPts D.sp.cm.sig (Jst D n) {v} : Set (G D n)) :=
    Subgroup.coe_inf _ _
  rw [e2]
  exact hK.inter_right hA

theorem exists_haar_prob {X : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [MeasurableSpace X]
    [BorelSpace X] (K₀ : Subgroup X) (h : IsCompact (K₀ : Set X)) :
    ∃ ν : Measure K₀, ν.IsHaarMeasure ∧ IsProbabilityMeasure ν := by
  have : CompactSpace K₀ := isCompact_iff_compactSpace.mp h
  refine ⟨Measure.haarMeasure ⊤, inferInstance, ⟨?_⟩⟩
  simpa using Measure.haarMeasure_self (G := K₀) (K₀ := ⊤)

theorem isLaw_sw {t : ℕ} {B : HSp D} (hB : B.rank = n + t) {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle}
    {θ : InfFam D} {μB : Measure (Mx D B.rank n)} {ωB : G D n →* Module.End ℂ (schwartzA θ B.rank n)}
    (hω : IsWeilSch ψ χ θ B μB ωB) (Φ : schwartzA θ B.rank n) :
    IsLaw χ ((t : ℂ) / 2) (fun g => (ωB g Φ).1 0) := by
  intro q hq a ha g
  obtain ⟨m, u, b, rfl, hm, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_levi_unip hq a ha
  have e' : ωB (m * u * g) Φ = ωB m (ωB u (ωB g Φ)) := by
    rw [map_mul, map_mul]; rfl
  have z1 : ((0 : Mx D B.rank n) ⬝ a.1 : Mx D B.rank n) = 0 := Matrix.zero_mul _
  have z2 : GlobalTheory.StdUnn.inner B (0 : Mx D B.rank n) 0 = 0 := by
    rw [GlobalTheory.StdUnn.inner, adj_zero, Matrix.zero_mul]
  have e3 : ((B.rank : ℂ) / 2) = (t : ℂ) / 2 + (n : ℂ) / 2 := by
    rw [hB]; push_cast; ring
  show (ωB (m * u * g) Φ).1 0 = _ * _ * (ωB g Φ).1 0
  rw [e', hω.levi m a hm, hω.unip u b hu, z1, z2, e3]
  simp [halfTr]

theorem theta_mul {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n))
    (Ψ : schwartzA θ V.rank n) (g u : G D n) (h : GA D V) : theta ω Ψ (g * u) h = theta ω (ω u Ψ) g h := by
  simp only [theta, map_mul]
  rfl

end PositivityTheory.Rg.Rsw.L.LResCore

end
end

