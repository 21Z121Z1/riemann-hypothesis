import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0160
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0429
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0404
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0036
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0128
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0217
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0135

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesSingleOrbitTamePlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

noncomputable section

open scoped TensorProduct

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.IwaOrbit

variable {D : D7}

theorem mul_mem_intAE {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem intAt_zero {P : Pl D → Prop} : (0 : AE D) ∈ intAt D P :=
  ⟨zero_mem _, by rw [(finPart D).map_zero]; exact zero_mem _⟩

theorem intAt_add {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) :
    a + b ∈ intAt D P :=
  ⟨add_mem ha.1 hb.1, by rw [(finPart D).map_add]; exact add_mem ha.2 hb.2⟩

theorem intAt_mul {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) :
    a * b ∈ intAt D P :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by rw [(finPart D).map_mul]; exact mul_mem_intAE ha.2 hb.2⟩

theorem mulVec_mem_intAt {P : Pl D → Prop} {m n : ℕ} {M : Matrix (Fin m) (Fin n) (AE D)} {z : Fin n → AE D}
    (hM : ∀ i j, M i j ∈ intAt D P) (hz : ∀ j, z j ∈ intAt D P) (i : Fin m) : (M *ᵥ z) i ∈ intAt D P := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_induction _ (· ∈ intAt D P) (fun _ _ => intAt_add) intAt_zero
    fun j _ => intAt_mul (hM i j) (hz j)

theorem mul_mem_idAt_left {P : Pl D → Prop} {l m n : ℕ} {A : Matrix (Fin l) (Fin m) (AE D)}
    (B : Matrix (Fin m) (Fin n) (AE D)) (hA : ∀ i j, A i j ∈ idAt D P) (i : Fin l) (j : Fin n) :
    (A * B) i j ∈ idAt D P := by
  rw [Matrix.mul_apply]; exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hA i k)

theorem mul_mem_idAt_right {P : Pl D → Prop} {l m n : ℕ} (A : Matrix (Fin l) (Fin m) (AE D))
    {B : Matrix (Fin m) (Fin n) (AE D)} (hB : ∀ i j, B i j ∈ idAt D P) (i : Fin l) (j : Fin n) :
    (A * B) i j ∈ idAt D P := by
  rw [Matrix.mul_apply]; exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hB k j)

theorem smul_eq_self {P : Pl D → Prop} {ε : AE D} (hε : ∀ a, a ∈ idAt D P ↔ ε * a = a) {m n : ℕ}
    {X : Matrix (Fin m) (Fin n) (AE D)} (hX : ∀ i j, X i j ∈ idAt D P) : ε • X = X := by
  ext i j; rw [Matrix.smul_apply, smul_eq_mul]; exact (hε _).1 (hX i j)

theorem smul_vec_eq_self {P : Pl D → Prop} {ε : AE D} (hε : ∀ a, a ∈ idAt D P ↔ ε * a = a) {n : ℕ}
    {y : Fin n → AE D} (hy : ∀ i, y i ∈ idAt D P) : ε • y = y := by
  funext i; rw [Pi.smul_apply, smul_eq_mul]; exact (hε _).1 (hy i)

theorem smul_mulVec' {m n : ℕ} (a : AE D) (A : Matrix (Fin m) (Fin n) (AE D)) (y : Fin n → AE D) :
    (a • A) *ᵥ y = a • (A *ᵥ y) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum, mul_assoc]

theorem adj_smul {m n : ℕ} (a : AE D) (X : Matrix (Fin m) (Fin n) (AE D)) : adj (a • X) = cA D a • adj X := by
  ext i j
  change cA D (a * X j i) = cA D a * cA D (X j i)
  exact (cA D).map_mul _ _

theorem adj_sub {m n : ℕ} (X Y : Matrix (Fin m) (Fin n) (AE D)) : adj (X - Y) = adj X - adj Y := by
  ext i j
  change cA D (X j i - Y j i) = cA D (X j i) - cA D (Y j i)
  exact (cA D).map_sub _ _

theorem adj_mem_idAt {P : Pl D → Prop} {ε : AE D} (hcε : cA D ε = ε) (hε : ∀ a, a ∈ idAt D P ↔ ε * a = a)
    {m n : ℕ} {X : Matrix (Fin m) (Fin n) (AE D)} (hX : ∀ i j, X i j ∈ idAt D P) (i : Fin n) (j : Fin m) :
    adj X i j ∈ idAt D P := by
  rw [hε]
  have h := congrArg (cA D) ((hε _).1 (hX j i))
  rw [(cA D).map_mul, hcε] at h
  exact h

theorem exists_onb (S : HSp D) (v : Pl D) (ε : AE D) (Λ : AddSubgroup (Fin S.rank → AE D)) (ht : Tame D v)
    (hεε : ε * ε = ε) (hcε : cA D ε = ε) (hεO : ε ∈ intAt D (· = v)) (hεI : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a)
    (hΛ : IsSDAt S v Λ) :
    ∃ b b' : Matrix (Fin S.rank) (Fin S.rank) (AE D), (∀ i j, b i j ∈ idAt D (· = v)) ∧
      (∀ i j, b' i j ∈ idAt D (· = v)) ∧ b * b' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ∧
      b' * b = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ∧
      (∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ ∀ i, (b' *ᵥ y) i ∈ intAt D (· = v))) ∧
      adj b * (gA S * b) = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
  obtain ⟨β, β', hβ, hβ', h1, h2, hmem, hHO, hHc, hH⟩ := GlobalTheory.T.exists_unimodular_basis_selfDual_lattice_at_place D S v ε Λ ht hεε hcε hεO hεI hΛ
  obtain ⟨P, P', hP, hP', hPP', hP'P, hPH⟩ := GlobalTheory.T.unimodular_hermitian_congr_one_at_tamePlace D v ε S.rank _ ht hεε hcε hεO hεI hHO hHc hH
  refine ⟨β * P, P' * β', mul_mem_idAt_left P hβ, mul_mem_idAt_right P' hβ', ?_, ?_, ?_, ?_⟩
  · calc β * P * (P' * β') = β * (P * P') * β' := by simp only [Matrix.mul_assoc]
      _ = ε • (β * β') := by rw [hPP', Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      _ = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by rw [h1, smul_smul, hεε]
  · calc P' * β' * (β * P) = P' * (β' * β) * P := by simp only [Matrix.mul_assoc]
      _ = ε • (P' * P) := by rw [h2, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      _ = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by rw [hP'P, smul_smul, hεε]
  · intro y hy
    rw [hmem y hy]
    constructor
    · intro h i
      rw [← Matrix.mulVec_mulVec]
      exact mulVec_mem_intAt hP' h i
    · intro h i
      have hz : β' *ᵥ y = P *ᵥ (P' *ᵥ (β' *ᵥ y)) := by
        rw [Matrix.mulVec_mulVec, hPP', smul_mulVec', Matrix.one_mulVec,
          smul_vec_eq_self hεI (mulVec_mem_idAt β' hy)]
      rw [hz]
      exact mulVec_mem_intAt hP (fun j => by rw [Matrix.mulVec_mulVec]; exact h j) i
  · rw [adj_mul, ← hPH]
    simp only [Matrix.mul_assoc]

theorem selfDual_orbit : ∀ (D : D7) (S₀ : HSp D) (v : Pl D) (Λ Λ' : AddSubgroup (Fin S₀.rank → AE D)), Tame D v → IsSDAt S₀ v Λ → IsSDAt S₀ v Λ' → ∃ γ ∈ grpAt S₀ (· = v), ∀ y : Fin S₀.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ mt S₀ γ *ᵥ y ∈ Λ') := by
  intro D S v Λ Λ' ht hΛ hΛ'
  obtain ⟨⟨ε, hεε, hcε, hεO, hεI, -⟩, -⟩ := GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)
  obtain ⟨b, b', hb, hb', hbb', hb'b, hmem, hG⟩ := exists_onb S v ε Λ ht hεε hcε hεO hεI hΛ
  obtain ⟨c, c', hc, hc', hcc', hc'c, hmem', hG'⟩ := exists_onb S v ε Λ' ht hεε hcε hεO hεI hΛ'
  set g := c * b' with hg
  have hgI : ∀ i j, g i j ∈ idAt D (· = v) := mul_mem_idAt_right c hb'
  have hag : ε • adj g = adj g := smul_eq_self hεI (adj_mem_idAt hcε hεI hgI)
  have hgg : ε • g = g := smul_eq_self hεI hgI
  have hb'b' : adj b' * b' = ε • gA S := by
    have h := congrArg (fun X => adj b' * X * b') hG
    rw [Matrix.mul_smul, Matrix.mul_one, smul_eq_self hεI (adj_mem_idAt hcε hεI hb')] at h
    rw [← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← adj_mul, Matrix.mul_assoc, Matrix.mul_assoc, hbb', adj_smul,
      adj_one, hcε, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hεε]
  have hf1 : adj g * (gA S * g) = ε • gA S := by
    rw [hg, adj_mul]
    calc adj b' * adj c * (gA S * (c * b')) = adj b' * (adj c * (gA S * c)) * b' := by simp only [Matrix.mul_assoc]
      _ = ε • gA S := by rw [hG', Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hb'b', smul_smul, hεε]
  have haG : adj g * gA S = ε • (adj g * gA S) := by rw [← Matrix.smul_mul, hag]
  have hGg : gA S * g = ε • (gA S * g) := by rw [← Matrix.mul_smul, hgg]
  have hunit : adj (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)))) ⬝ (gA S ⬝ (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D))))) = gA S := by
    show adj (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)))) * (gA S * (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D))))) = gA S
    rw [adj_add, adj_sub, adj_one, adj_smul, adj_one, hcε]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
    rw [hf1]
    simp only [smul_add, smul_sub]
    rw [← haG, ← hGg, smul_smul, hεε]
    abel
  refine ⟨ofMat S (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)))) hunit, ?_, ?_⟩
  · refine (mem_congGrp_iff S (idAt D (· = v)) _).2 fun i j => ?_
    show (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)))) i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j ∈ idAt D (· = v)
    have e : (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)))) i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j =
        g i j - ε * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j := by
      rw [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
    rw [e]
    exact sub_mem (hgI i j) (Ideal.mul_mem_right _ _ hεO.1)
  · intro y hy
    have hMy : mt S (ofMat S (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)))) hunit) *ᵥ y = g *ᵥ y := by
      show (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)))) *ᵥ y = g *ᵥ y
      rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, smul_mulVec', Matrix.one_mulVec,
        smul_vec_eq_self hεI hy, sub_self, add_zero]
    rw [hMy, hmem y hy, hmem' _ (mulVec_mem_idAt g hy)]
    have : c' *ᵥ (g *ᵥ y) = b' *ᵥ y := by
      rw [Matrix.mulVec_mulVec, hg, ← Matrix.mul_assoc, hc'c, Matrix.smul_mul, Matrix.one_mul,
        smul_eq_self hεI hb']
    rw [this]

end GlobalTheory.IwaOrbit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitFrameGLFiniteMatrixOffPlaceEqOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm

namespace GlobalTheory.StabOff

set_option synthInstance.maxHeartbeats 200000

theorem prV_comm_tmul {D : D7} (v : Pl D) (a : Af ↥D.host.F) (e : D.host.E) :
    Formalism.UG.prV (E := D.host.E) v ((Algebra.TensorProduct.comm (↥D.host.F) (Af ↥D.host.F) D.host.E) (a ⊗ₜ e)) =
      (Algebra.TensorProduct.comm _ _ _) (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v (a ⊗ₜ e)) := by
  rw [Algebra.TensorProduct.comm_tmul]
  simp only [Formalism.UG.prV, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.comm_tmul]
  rfl

theorem prV_comm {D : D7} (v : Pl D) (z : Af ↥D.host.F ⊗[↥D.host.F] D.host.E) :
    Formalism.UG.prV (E := D.host.E) v ((Algebra.TensorProduct.comm (↥D.host.F) (Af ↥D.host.F) D.host.E) z) =
      (Algebra.TensorProduct.comm _ _ _) (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul a e => exact prV_comm_tmul v a e
  | add a b ha hb =>
    simp only [map_add]
    exact congrArg₂ (· + ·) ha hb

theorem prV_toEAf_eq_zero {D : D7} (v : Pl D) (y : AE D) (h : FinPl.compAt D v y = 0) :
    Formalism.UG.prV (E := D.host.E) v (toEAf D y) = 0 := by
  unfold FinPl.compAt at h
  unfold toEAf
  simp only [RingHom.comp_apply] at h ⊢
  generalize finPart D y = z at h ⊢
  refine (prV_comm v z).trans ?_
  rw [h, map_zero]

theorem compAt_mt {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n) (g : GL n k) (v : Pl D)
    (hv : v ≠ p.v) (i j : Fin S.rank) :
    FinPl.compAt D v (Formalism.L2.Theta.mt S (β.gl g) i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) = 0 := by
  have hmem : β.gl g ∈ grpAt S (· = p.v) := ((GlobalTheory.T.splitPlaceHermitianFrame_properties D k p S n β).1 _).2 ⟨g, rfl⟩
  unfold grpAt congGrp at hmem
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hmem
  have h1 := congrArg (fun u => u.1 i j) hmem
  simp only [GeneralLinearGroup.map_apply, Units.val_one] at h1
  have h2 : Ideal.Quotient.mk (idAt D (· = p.v)) (Formalism.L2.Theta.mt S (β.gl g) i j) =
      Ideal.Quotient.mk (idAt D (· = p.v)) ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) := by
    refine h1.trans ?_
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [Ideal.Quotient.eq] at h2
  unfold idAt at h2
  rw [Ideal.mem_inf] at h2
  have h3 := h2.2
  rw [Submodule.mem_iInf] at h3
  exact (RingHom.mem_ker).1 (h3 ⟨v, hv⟩)

theorem bc_prV_finM_eq_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (g : GL n k) (m : ℕ) (hm : S.rank = m) (x : GL (Fin m) (EF D)), x.1 = finM S hm (β.gl g) → ∀ v : Pl D, v ≠ p.v → Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x = 1 := by
  intro D k _ _ _ _ p S n _ _ β g m hm x hx v hv
  apply Units.ext
  ext i j
  change Formalism.UG.prV (E := D.host.E) v (x.1 i j) = (1 : Matrix (Fin m) (Fin m) _) i j
  rw [hx]
  simp only [GlobalTheory.AdForm.finM, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
  have h := prV_toEAf_eq_zero v _ (compAt_mt β g v hv ((finCongr hm).symm i) ((finCongr hm).symm j))
  rw [map_sub, map_sub, sub_eq_zero] at h
  rw [h]
  by_cases hij : i = j
  · subst hij
    simp [Matrix.one_apply]
  · have hij' : (finCongr hm).symm i ≠ (finCongr hm).symm j := fun e => hij ((finCongr hm).symm.injective e)
    simp [Matrix.one_apply, hij, hij']

end GlobalTheory.StabOff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjPartLineMultipleMemIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ColsConj

theorem form_mulVec {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (A : Fin N → k)
    (G : Fin N → Fin N → k) (β : Matrix (Fin N) Y k) (m₁ : Y) (c₁ : k)
    (h1 : ∑ r, ∑ r', A r * G r r' * β r' m₁ = c₁) (h0 : ∀ m, m ≠ m₁ → ∑ r, ∑ r', A r * G r r' * β r' m = 0)
    (w : Y → k) : ∑ r, ∑ r', A r * G r r' * (β *ᵥ w) r' = c₁ * w m₁ := by
  have h : ∑ r, ∑ r', A r * G r r' * (β *ᵥ w) r' = ∑ m, (∑ r, ∑ r', A r * G r r' * β r' m) * w m := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm (s := (Finset.univ : Finset Y))]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_comm (s := (Finset.univ : Finset Y))]
    refine Finset.sum_congr rfl fun r' _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [h, Finset.sum_eq_single m₁ (fun m _ hm => by rw [h0 m hm, zero_mul]) (fun hm => absurd (Finset.mem_univ _) hm), h1]

theorem conj_part_mem_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y) (u u' : Fin S.rank → D.host.E) (m₁ : Y) (c₁ : k), IsSelfDualC S L → IntIn q S F L → valuation k c₁ = 1 → (∀ r, F.β r m₁ = c₁ * (ofSplit q).pr (u' r)) → (∑ r, ∑ r', star (u r) * S.gram r r' * u' r' = 1) → (∀ m, m ≠ m₁ → ∑ r, ∑ r', (ofSplit q).pr (star (u r)) * (ofSplit q).pr (S.gram r r') * F.β r' m = 0) → ∀ a : AE D, ((fun r => cA D q.e * (a * incA D (u r))) ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ q.pr (cA D a) ∈ 𝒪[k]) := by
  intro D k _ _ _ _ q S L Y _ _ F u u' m₁ c₁ hL hI hc hb hd hp a
  have hpr : ∀ x : D.host.E, (ofSplit q).pr x = q.pr (incA D x) := fun _ => rfl
  simp only [hpr] at hb hp
  have hy : (fun r => cA D q.e * (a * incA D (u r))) =
      fun r => cA D (q.sec (q.pr (cA D a) * q.pr (incA D (star (u r))))) := by
    funext r
    rw [← RingHom.map_mul, q.sec_pr, RingHom.map_mul, RingHom.map_mul, GlobalTheory.LatVac.cA_cA,
      GlobalTheory.FinPl.FrameLat.cA_incA, star_star]
  have h1 : ∑ r, ∑ r', q.pr (incA D (star (u r))) * q.pr (incA D (S.gram r r')) * F.β r' m₁ = c₁ := by
    have h := congrArg (fun x => c₁ * q.pr (incA D x)) hd
    simp only [map_sum, RingHom.map_mul, RingHom.map_one, mul_one, Finset.mul_sum] at h
    rw [← h]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => ?_
    rw [hb]; ring
  have key : ∀ w : Y → k, ∑ i, ∑ j, (F.β *ᵥ w) i * q.pr (cA D (incA D (S.gram i j))) *
      (q.pr (cA D a) * q.pr (incA D (star (u j)))) = q.pr (cA D a) * (c₁ * w m₁) := by
    intro w
    rw [← form_mulVec _ _ F.β m₁ c₁ h1 hp w, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [GlobalTheory.FinPl.FrameLat.cA_incA, GlobalTheory.LatVac.gram_star]; ring
  rw [hy, GlobalTheory.FinPl.FrameLat.csec_mem_iff hL]
  constructor
  · intro h
    have hw : ∀ i, (Pi.single m₁ (1 : k) : Y → k) i ∈ 𝒪[k] := fun i => by
      rw [Pi.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have h2 := h _ ((hI _).1 hw)
    rw [key, Pi.single_eq_same, mul_one] at h2
    rw [Valuation.mem_integer_iff] at h2 ⊢
    rwa [map_mul, hc, mul_one] at h2
  · intro ha x hx
    have hxe : x = F.β *ᵥ (F.γ *ᵥ x) := by rw [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec]
    have hw : ∀ i, (F.γ *ᵥ x) i ∈ 𝒪[k] := (hI _).2 (by rw [← hxe]; exact hx)
    rw [hxe, key]
    exact mul_mem ha (mul_mem ((Valuation.mem_integer_iff _ _).2 hc.le) (hw m₁))

end GlobalTheory.ColsConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceFrameGLMemCompactRealTrivial
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm

noncomputable section

namespace GlobalTheory.FrameGfC

theorem gl_mem_GfC : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (g : GL n k), β.gl g ∈ GfC S := by
  intro D k _ _ _ _ p S n _ _ β g
  have hg := β.gl_supp g
  have he := p.split
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h : infPart D ((mt S (β.gl g) - 1) i j) = 0 := by
    rw [← hg i j, RingHom.map_mul, RingHom.map_add, GlobalTheory.SplitScalar.infPart_splitIdem he,
      GlobalTheory.SplitScalar.infPart_splitIdem (GlobalTheory.SplitScalar.isSplitIdem_conj he), add_zero, zero_mul]
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at h
  show infPart D (mt S (β.gl g) i j) = (1 : Matrix _ _ _) i j
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [RingHom.map_one]
  · rw [RingHom.map_zero]

end GlobalTheory.FrameGfC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceFrameMovedBackIsLatticeBasis
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.FrameBack

theorem idAt_of_place {D : D7} (P : Pl D → Prop) (v : Pl D) (hv : P v) {a : AE D} (h : a ∈ idAt D (· = v)) :
    a ∈ idAt D P := by
  simp only [idAt, Submodule.mem_inf, Submodule.mem_iInf] at h ⊢
  exact ⟨h.1, fun w => h.2 ⟨w.1, fun hw => w.2 (hw ▸ hv)⟩⟩

theorem mem_latV_iff {D : D7} (S : HSp D) (L : Lat S) (hL : Submodule.IsLattice D.host.E L) (P : Pl D → Prop)
    (v : Pl D) (hv : P v) (y : Fin S.rank → AE D) (hy : ∀ i, y i ∈ idAt D (· = v)) :
    y ∈ latV S L P ↔ y ∈ latV S L (· = v) := by
  have hT := ((GlobalTheory.FinPl.localComponents D P).2 S).2.2.2 L y hL
  have hV := ((GlobalTheory.FinPl.localComponents D (· = v)).2 S).2.2.2 L y hL
  rw [hT, hV]
  constructor
  · rintro ⟨_, h⟩
    exact ⟨hy, fun w hw e he => h w (hw ▸ hv) e he⟩
  · rintro ⟨_, h⟩
    refine ⟨fun i => idAt_of_place P v hv (hy i), fun w _ e he => ?_⟩
    by_cases hwv : w = v
    · exact h w hwv e he
    · obtain ⟨ε, -, -, -, hAt, hOff⟩ := (GlobalTheory.FinPl.localComponents D (· = w)).1
      have hzero : e • y = 0 := by
        funext i
        have hyi : y i ∈ idOff D (· = w) := by
          have h' := hy i
          simp only [idAt, Submodule.mem_inf, Submodule.mem_iInf] at h'
          simp only [idOff, Submodule.mem_iInf]
          intro u
          have := h'.2 ⟨u.1, by rw [u.2]; exact hwv⟩
          exact this
        have h1 : ε * e = e := (hAt e).1 he.1
        have h2 : ε * y i = 0 := (hOff (y i)).1 hyi
        show e * y i = 0
        rw [← h1, mul_comm ε e, mul_assoc, h2, mul_zero]
      rw [hzero]
      exact (latV S L (· = w)).zero_mem

theorem mul_sec {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : SplitPt D k) (a : AE D) (x : k) : a * q.sec x = q.sec (q.pr a * x) := by
  have h : q.e * q.sec x = q.sec x := by rw [← q.sec_pr, q.pr_sec]
  have h2 := q.sec_pr (a * q.sec x)
  rw [map_mul, q.pr_sec, mul_left_comm, h] at h2
  exact h2.symm

theorem frame_back : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) (g : GA D V) (L N : GlobalTheory.FinPl.Lat V) (P : GlobalTheory.FinPl.Pl D → Prop), P q.v → IsSelfDualC V L → IsSelfDualC V N → GlobalTheory.FinPl.Moves V g L N P → ∀ (Y : Type) [Fintype Y] (β β' : Matrix (Fin V.rank) Y k), β = (Formalism.L2.Theta.mt V g).map q.pr * β' → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV V N (· = q.v)) → ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((β' *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV V L (· = q.v) := by
  intro D k _ _ _ _ q V g L N P hP hL hN hM Y _ β β' hβ hb y
  have hmv : Formalism.L2.Theta.mt V g *ᵥ (fun i => q.sec ((β' *ᵥ y) i)) = fun i => q.sec ((β *ᵥ y) i) := by
    funext i
    rw [hβ, ← Matrix.mulVec_mulVec]
    generalize β' *ᵥ y = z
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, mul_sec]
  have hu : ∀ i, (fun i => q.sec ((β' *ᵥ y) i)) i ∈ idAt D (· = q.v) := fun i => q.sec_mem_idAt _
  have hu' : ∀ i, (fun i => q.sec ((β *ᵥ y) i)) i ∈ idAt D (· = q.v) := fun i => q.sec_mem_idAt _
  rw [hb y, ← mem_latV_iff V N hN.1 P q.v hP _ hu', ← mem_latV_iff V L hL.1 P q.v hP _ hu,
    hM _ (fun i => idAt_of_place P q.v hP (hu i)), hmv]

end GlobalTheory.FinPl.FrameBack
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIntegralAdeleIffBothComponents
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SplitInt

theorem intAt_iff_pr (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (a : AE D) (ha : a ∈ GlobalTheory.FinPl.idAt D (· = q.v)) :
    (a ∈ GlobalTheory.FinPl.intAt D (· = q.v) ↔ q.pr a ∈ 𝒪[k] ∧ q.pr (cA D a) ∈ 𝒪[k]) := by
  have he := GlobalTheory.UpMem.finPart_e_int q
  rw [q.int_iff, q.int_iff, q.sec_pr, q.sec_pr, map_mul, map_mul]
  constructor
  · rintro ⟨-, h⟩
    exact ⟨GlobalTheory.FinPl.FrameLat.mul_mem_intAE he h,
      GlobalTheory.FinPl.FrameLat.mul_mem_intAE he (GlobalTheory.IdemSupport.finPart_cA_mem h)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨ha, ?_⟩
    have hsum : a = q.e * a + cA D (q.e * cA D a) := by
      rw [map_mul, Formalism.L2.Theta.cA_cA, ← add_mul]
      exact ((GlobalTheory.FinPl.FrameLat.idem_iff q a).1 ha).symm
    have h3 : finPart D (cA D (q.e * cA D a)) ∈ intAE D := by
      apply GlobalTheory.IdemSupport.finPart_cA_mem
      rw [map_mul]; exact h2
    rw [hsum, (finPart D).map_add, (finPart D).map_mul]
    exact add_mem h1 h3

end GlobalTheory.SplitInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceMemLatticeCompletionIffParts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.SplitParts

theorem mem_latV_iff_parts : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (y : Fin S.rank → AE D), (∀ r, y r ∈ GlobalTheory.FinPl.idAt D (· = q.v)) → (y ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ (fun r => q.e * y r) ∈ GlobalTheory.FinPl.latV S L (· = q.v) ∧ (fun r => cA D q.e * y r) ∈ GlobalTheory.FinPl.latV S L (· = q.v)) := by
  intro D k _ _ _ _ q S L y hy
  have he : finPart D q.e ∈ intAE D := GlobalTheory.UpMem.finPart_e_int q
  have hce : finPart D (cA D q.e) ∈ intAE D := (GlobalTheory.FinPl.FrameLat.cA_int_iff q.e).2 he
  constructor
  · intro h
    exact ⟨GlobalTheory.FinPl.LatIndHalf.mul_mem_latV he h, GlobalTheory.FinPl.LatIndHalf.mul_mem_latV hce h⟩
  · rintro ⟨h1, h2⟩
    have e : y = (fun r => q.e * y r) + (fun r => cA D q.e * y r) := by
      funext r
      rw [Pi.add_apply, ← add_mul, (GlobalTheory.FinPl.FrameLat.idem_iff q (y r)).1 (hy r)]
    rw [e]
    exact add_mem h1 h2

end GlobalTheory.FinPl.SplitParts
end
end

