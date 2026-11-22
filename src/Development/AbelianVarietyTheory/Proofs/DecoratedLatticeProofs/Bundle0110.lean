import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0105
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReducedBasisBoundedTypeOfInstance
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRingEquivPadicOfResidueCardUniformizer
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedLatticeFiniteExpansionsLocalField

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsotropicDualColumnsSelfDualLatticeAtPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open scoped TensorProduct

namespace GlobalTheory.IwaPlace.DualIso

variable {D : D7}

theorem intAE_mul_mem' {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
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

theorem intAt_mul_mem {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_left _ _ hb.1, by rw [map_mul]; exact intAE_mul_mem' ha.2 hb.2⟩

theorem hermAt_smul_left (S : HSp D) (o : AE D) (y x : Fin S.rank → AE D) :
    hermAt S (o • y) x = o * hermAt S y x := by
  simp only [hermAt, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem smul_mem_of_isSDAt {S : HSp D} {v : Pl D} {M : AddSubgroup (Fin S.rank → AE D)} (hM : IsSDAt S v M)
    {o : AE D} (ho : o ∈ intAt D (· = v)) {y : Fin S.rank → AE D} (hy : y ∈ M) : o • y ∈ M := by
  refine (hM.2.2 _ fun i => ?_).2 fun x hx => ?_
  · simp only [Pi.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_left _ _ (hM.1 y hy i)
  · rw [hermAt_smul_left]; exact intAt_mul_mem ho ((hM.2.2 y (hM.1 y hy)).1 hy x hx)

theorem col_mul_mem {S : HSp D} {v : Pl D} {M : AddSubgroup (Fin S.rank → AE D)} (hM : IsSDAt S v M) {ρ : ℕ}
    (A : Mx D S.rank ρ) (B : Mx D ρ ρ) (hA : ∀ i, (fun k => A k i) ∈ M) (hB : ∀ m i, B m i ∈ intAt D (· = v))
    (i : Fin ρ) : (fun k => (A ⬝ B) k i) ∈ M := by
  have e : (fun k => (A ⬝ B) k i) = ∑ m, B m i • (fun k => A k m) := by
    funext k; simp [Matrix.mul_apply, Finset.sum_apply, mul_comm]
  rw [e]; exact AddSubgroup.sum_mem _ fun m _ => smul_mem_of_isSDAt hM (hB m i) (hA m)

theorem gram_entry (S : HSp D) {ρ : ℕ} (c' : Mx D S.rank ρ) (i j : Fin ρ) :
    (adj c' ⬝ (gA S ⬝ c')) i j = hermAt S (fun k => c' k j) (fun k => c' k i) := by
  simp only [hermAt, adj, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, mul_assoc]

theorem smul_mul_smul_one {ρ : ℕ} (ε w : AE D) (H : Mx D ρ ρ) : (ε • (1 : Mx D ρ ρ)) ⬝ (w • H) = (ε * w) • H := by
  rw [smul_mul_assoc, one_mul, smul_smul]

theorem smul_mul_smul_one' {ρ : ℕ} (ε w : AE D) (H : Mx D ρ ρ) : (w • H) ⬝ (ε • (1 : Mx D ρ ρ)) = (ε * w) • H := by
  rw [mul_smul_comm, mul_one, smul_smul]

theorem adj_gram_self (S : HSp D) {ρ : ℕ} (c' : Mx D S.rank ρ) : adj (adj c' ⬝ (gA S ⬝ c')) = adj c' ⬝ (gA S ⬝ c') := by
  rw [adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]

theorem gram_swap_smul (S : HSp D) {ρ : ℕ} {ε : AE D} (hεc : cA D ε = ε) (c c' : Mx D S.rank ρ)
    (hcc : adj c' ⬝ (gA S ⬝ c) = ε • (1 : Mx D ρ ρ)) : adj c ⬝ (gA S ⬝ c') = ε • (1 : Mx D ρ ρ) := by
  have := congrArg adj hcc
  rwa [adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc, adj_smul, hεc, adj_one] at this

theorem pair_sub (S : HSp D) {ρ : ℕ} {ε : AE D} (c c' : Mx D S.rank ρ) (K : Mx D ρ ρ)
    (hcc0 : adj c ⬝ (gA S ⬝ c) = 0) (hcc : adj c' ⬝ (gA S ⬝ c) = ε • (1 : Mx D ρ ρ)) :
    adj (c' - c ⬝ K) ⬝ (gA S ⬝ c) = ε • (1 : Mx D ρ ρ) := by
  rw [adj_sub, adj_mul, Matrix.sub_mul, Matrix.mul_assoc, hcc0, Matrix.mul_zero, sub_zero, hcc]

theorem pair_sub' (S : HSp D) {ρ : ℕ} {ε : AE D} (c c' : Mx D S.rank ρ) (K : Mx D ρ ρ)
    (hcc' : adj c ⬝ (gA S ⬝ c') = ε • (1 : Mx D ρ ρ)) :
    adj (c' - c ⬝ K) ⬝ (gA S ⬝ c') = adj c' ⬝ (gA S ⬝ c') - adj K ⬝ (ε • (1 : Mx D ρ ρ)) := by
  rw [adj_sub, adj_mul, Matrix.sub_mul, Matrix.mul_assoc, hcc']

theorem self_sub (S : HSp D) {ρ : ℕ} (c'' c c' : Mx D S.rank ρ) (K : Mx D ρ ρ) (h : c'' = c' - c ⬝ K) :
    adj c'' ⬝ (gA S ⬝ c'') = adj c'' ⬝ (gA S ⬝ c') - adj c'' ⬝ (gA S ⬝ c) ⬝ K := by
  rw [h, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc (gA S) c K,
    ← Matrix.mul_assoc (adj (c' - c ⬝ K)) (gA S ⬝ c) K]

theorem isotropic_core {S : HSp D} {v : Pl D} {ε : AE D} (hεε : ε * ε = ε) (hεc : cA D ε = ε)
    (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) {M : AddSubgroup (Fin S.rank → AE D)} (hM : IsSDAt S v M)
    {w : AE D} (hw : w ∈ intAt D (· = v)) (hwc : w + cA D w = ε) {ρ : ℕ} (c c' : Mx D S.rank ρ)
    (hc : ∀ i, (fun k => c k i) ∈ M) (hc' : ∀ i, (fun k => c' k i) ∈ M) (hcc0 : adj c ⬝ (gA S ⬝ c) = 0)
    (hcc : adj c' ⬝ (gA S ⬝ c) = ε • (1 : Mx D ρ ρ)) :
    ∃ c'' : Mx D S.rank ρ, (∀ i, (fun k => c'' k i) ∈ M) ∧ adj c'' ⬝ (gA S ⬝ c) = ε • (1 : Mx D ρ ρ) ∧
      adj c'' ⬝ (gA S ⬝ c'') = 0 := by
  obtain ⟨H, hH⟩ : ∃ H : Mx D ρ ρ, H = adj c' ⬝ (gA S ⬝ c') := ⟨_, rfl⟩
  have hHint : ∀ i j, H i j ∈ intAt D (· = v) := fun i j => by
    rw [hH, gram_entry]; exact (hM.2.2 _ (hM.1 _ (hc' j))).1 (hc' j) _ (hc' i)
  have hεH : ε • H = H := by
    funext i j; rw [Matrix.smul_apply, smul_eq_mul]; exact (hε _).1 (hHint i j).1
  have hadjH : adj H = H := by rw [hH]; exact adj_gram_self S c'
  have hcc' := gram_swap_smul S hεc c c' hcc
  have hKint : ∀ m i, (w • H) m i ∈ intAt D (· = v) := fun m i => by
    rw [Matrix.smul_apply, smul_eq_mul]; exact intAt_mul_mem hw (hHint m i)
  have e3 : ε * cA D w + ε * w = ε := by rw [← mul_add, add_comm, hwc, hεε]
  have f3 : H - (ε * cA D w) • H - (ε * w) • H = 0 := by
    rw [sub_sub, ← add_smul, e3, hεH, sub_self]
  have e1 := pair_sub S (ε := ε) c c' (w • H) hcc0 hcc
  have e2 := pair_sub' S c c' (w • H) hcc'
  rw [← hH, adj_smul, hadjH, smul_mul_smul_one'] at e2
  refine ⟨c' - c ⬝ (w • H), fun i => ?_, e1, ?_⟩
  · have e : (fun k => (c' - c ⬝ (w • H)) k i) = (fun k => c' k i) - fun k => (c ⬝ (w • H)) k i := rfl
    rw [e]; exact sub_mem (hc' i) (col_mul_mem hM c _ hc hKint i)
  · rw [self_sub S _ c c' (w • H) rfl, e1, e2, smul_mul_smul_one, f3]
theorem dual_isotropic : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) (M : AddSubgroup (Fin S.rank → AE D)), IsSDAt S v M → ∀ w ∈ intAt D (· = v), w + cA D w = ε → ∀ (b : Mx D ρ ρ) (c' : Mx D S.rank ρ), (∀ i j, b i j ∈ idAt D (· = v)) → (∀ i, (fun k => (d.jX ⬝ b) k i) ∈ M) → (∀ i, (fun k => c' k i) ∈ M) → adj c' ⬝ (gA S ⬝ (d.jX ⬝ b)) = ε • (1 : Mx D ρ ρ) → ∃ c'' : Mx D S.rank ρ, (∀ i, (fun k => c'' k i) ∈ M) ∧ adj c'' ⬝ (gA S ⬝ (d.jX ⬝ b)) = ε • (1 : Mx D ρ ρ) ∧ adj c'' ⬝ (gA S ⬝ c'') = 0 := by
  intro D S S₀ ρ d v ε hεε hεc hεI hε M hM w hw hwc b c' hb hc hc' hcc
  have hcc0 : adj (d.jX ⬝ b) ⬝ (gA S ⬝ (d.jX ⬝ b)) = 0 := by
    rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S) d.jX b, ← Matrix.mul_assoc (adj d.jX),
      d.gram_XX, Matrix.zero_mul, Matrix.mul_zero]
  exact isotropic_core hεε hεc hε hM hw hwc (d.jX ⬝ b) c' hc hc' hcc0 hcc

end GlobalTheory.IwaPlace.DualIso

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOpenAddSubgroupFinitePoints
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Topology

namespace GlobalTheory.FinSubgroup

theorem exists_openAddSubgroup_finite_points :
    ∀ (D : D7) (V : Set (AE D)), V ∈ nhds (0 : AE D) →
      ∃ U : AddSubgroup (AE D), IsOpen (U : Set (AE D)) ∧ ∀ a ∈ U, infPart D a = 0 → a ∈ V := by
  intro D V hV
  obtain ⟨e, he, hc, hcs⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  letI : TopologicalSpace (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)
  letI : TopologicalSpace (InfiniteAdeleRing D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (InfiniteAdeleRing D.host.F) (InfiniteAdeleRing D.host.F ⊗[D.host.F] D.host.E)
  have h0 : e.symm 0 = 0 := map_zero _
  have hV' : (e.symm : _ → AE D) ⁻¹' V ∈ 𝓝 ((0 : InfiniteAdeleRing D.host.F ⊗[D.host.F] D.host.E),
      (0 : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) := by
    apply hcs.continuousAt.preimage_mem_nhds
    have : (e.symm : _ → AE D) (0, 0) = 0 := h0
    rw [this]
    exact hV
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 hV'
  obtain ⟨N, hN, hNB⟩ := (GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat D.host.F D.host.E 0 ⊤ (Subsingleton.elim _ _)).2 B hB
  let W : AddSubgroup (GlobalTheory.AdLat.RA D.host.F D.host.E) :=
    (GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E))).map (nsmulAddMonoidHom N)
  have hW : IsOpen (W : Set (GlobalTheory.AdLat.RA D.host.F D.host.E)) := by
    have := GlobalTheory.IdeleParts.isOpen_nsmul_adelicCompletion_integers D.host.F D.host.E N hN
    convert this using 1
    ext z
    simp only [W, AddSubgroup.coe_map, Set.mem_image, SetLike.mem_coe, nsmulAddMonoidHom_apply, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  let f : AE D →+ GlobalTheory.AdLat.RA D.host.F D.host.E := (AddMonoidHom.snd _ _).comp e.toAddMonoidHom
  have hf : Continuous f := continuous_snd.comp hc
  refine ⟨W.comap f, hW.preimage hf, fun a ha hinf => ?_⟩
  have h1 : (e a).1 = 0 := by rw [(he a).1]; exact hinf
  have h2 : (e a).2 ∈ B := by
    obtain ⟨y, hy, hya⟩ := AddSubgroup.mem_map.1 (AddSubgroup.mem_comap.1 ha)
    have : f a = (e a).2 := rfl
    rw [← this, ← hya]
    exact hNB y hy
  have h3 : e a ∈ A ×ˢ B := ⟨by rw [h1]; exact mem_of_mem_nhds hA, h2⟩
  have := hAB h3
  simpa using this

end GlobalTheory.FinSubgroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReducedBasisBoundedTypeOfInstanceStatement
section
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsReducedBasisBoundedType_of_instance : ∀ I : AutInst, RedBasis I := by
  first | exact @GlobalTheory.CuspGeo.redBasis_holds | exact GlobalTheory.CuspGeo.redBasis_holds | (intros; apply GlobalTheory.CuspGeo.redBasis_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRingEquivPadicOfResidueCardUniformizerStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringEquiv_padic_of_residueCard_uniformizer : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [IsTopologicalRing k] [CharZero k] (T : ℕ) [Fact T.Prime], Nat.card (IsLocalRing.ResidueField 𝒪[k]) = T → Irreducible (T : 𝒪[k]) → ∃ φ : ℚ_[T] ≃+* k, Continuous φ ∧ Continuous φ.symm ∧ ∀ x : ℚ_[T], φ x ∈ 𝒪[k] ↔ ‖x‖ ≤ 1 := by
  first | exact @GlobalTheory.QpChar.exists_ringEquiv_padic | exact GlobalTheory.QpChar.exists_ringEquiv_padic | (intros; apply GlobalTheory.QpChar.exists_ringEquiv_padic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTransvectionFixingFirstVectorsSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TransvMid

open GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction

variable {D : D7}

theorem form_mulVec (S : HSp D) {n : ℕ} (y : VA S) (M : Mx D S.rank n) (c : Fin n → AE D) :
    form S y (M *ᵥ c) = (fun k => cA D (c k)) ⬝ᵥ ((adj M ⬝ gA S) *ᵥ y) := by
  have h : (fun i => cA D ((M *ᵥ c) i)) = M.map (cA D) *ᵥ fun k => cA D (c k) := by
    funext i; exact RingHom.map_mulVec (cA D) M c i
  rw [form, h, ← Matrix.mulVec_mulVec]
  conv_rhs => rw [Matrix.dotProduct_mulVec, adj, Matrix.vecMul_transpose]

theorem mul_apply_col {m n k : ℕ} (g : Mx D m n) (M : Mx D n k) (r : Fin m) (c : Fin k) :
    (g ⬝ M) r c = (g *ᵥ (M *ᵥ Pi.single c 1)) r := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one]; rfl

theorem col_apply {m n : ℕ} (M : Mx D m n) (c : Fin n) (r : Fin m) : (M *ᵥ Pi.single c 1) r = M r c := by
  rw [Matrix.mulVec_single_one]; rfl

theorem submatrix_col {m n : ℕ} (M : Mx D m n) (i : Fin n) (c : Fin 1) :
    (M.submatrix id fun _ : Fin 1 => i) *ᵥ Pi.single c 1 = M *ᵥ Pi.single i 1 := by
  funext r; rw [col_apply, col_apply]; rfl

theorem smul_vecMulVec_single {ρ : ℕ} (s : AE D) (x : Fin ρ → AE D) (J k : Fin ρ) :
    (s • vecMulVec x (Pi.single J 1)) *ᵥ Pi.single k 1 = (s * (Pi.single k 1 : Fin ρ → AE D) J) • x := by
  funext l
  rw [col_apply]
  by_cases hk : k = J
  · subst hk; simp [Matrix.vecMulVec_apply]
  · simp [Matrix.vecMulVec_apply, Pi.single_eq_of_ne hk, Pi.single_eq_of_ne' hk]

theorem upSum_smul_vecMulVec {ρ : ℕ} (s : AE D) (x : Fin ρ → AE D) (j J : Fin ρ) (hJ : J.1 = j.1 + 1) :
    GlobalTheory.MixPer.upSum (s • vecMulVec x (Pi.single J 1)) = s * x j := by
  have hTe : ∀ i k : Fin ρ, (if k.1 = i.1 + 1 then (s • vecMulVec x (Pi.single J 1)) i k else 0) =
      if i = j then (if k = J then s * x j else 0) else 0 := by
    intro i k
    by_cases hk : k = J
    · subst hk
      by_cases hi : i = j
      · subst hi
        simp [hJ, Matrix.vecMulVec_apply, mul_comm]
      · have : ¬ (k.1 = i.1 + 1) := fun h => hi (Fin.ext (by omega))
        simp [hi, this]
    · simp [hk, Matrix.vecMulVec_apply]
  rw [GlobalTheory.MixPer.upSum]
  simp only [hTe]
  simp

section Mid

variable {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ)

theorem form_jY_single (y : VA V) (J : Fin ρ) (s : AE D) :
    form V y (d.jY *ᵥ Pi.single J (cA D s)) = s * (d.pX *ᵥ y) J := by
  have h : (fun k => cA D ((Pi.single J (cA D s) : Fin ρ → AE D) k)) = (Pi.single J s : Fin ρ → AE D) := by
    funext k
    by_cases hk : k = J
    · subst hk; simp [cA_cA]
    · simp [Pi.single_apply, hk]
  rw [form_mulVec, h, ← d.pX_eq, single_dotProduct]

theorem form_jX (y : VA V) (b : Fin ρ → AE D) :
    form V y (d.jX *ᵥ b) = (fun k => cA D (b k)) ⬝ᵥ (d.pY *ᵥ y) := by
  rw [form_mulVec, ← d.pY_eq]

theorem transv_fix {w v : VA V} {u : GA D V} (hu : IsTransv V w v u) {y : VA V} (hv : form V y v = 0)
    (hw : form V y w = 0) : mt V u *ᵥ y = y := by
  have := hu y
  rw [act, transv, hv, hw] at this
  rw [this]; simp

theorem pX_jX_single (k : Fin ρ) : d.pX *ᵥ (d.jX *ᵥ Pi.single k 1) = Pi.single k 1 := by
  rw [Matrix.mulVec_mulVec, d.pX_jX, Matrix.one_mulVec]

theorem pY_jX_vec (x : Fin ρ → AE D) : d.pY *ᵥ (d.jX *ᵥ x) = 0 := by
  rw [Matrix.mulVec_mulVec, d.pY_jX, Matrix.zero_mulVec]

theorem isotropicProjection_anisotropic_vec_eq_zero (x : Fin V₀.rank → AE D) : d.pX *ᵥ (d.j0 *ᵥ x) = 0 := by
  rw [Matrix.mulVec_mulVec, d.pX_j0, Matrix.zero_mulVec]

theorem dualProjection_anisotropic_vec_eq_zero (x : Fin V₀.rank → AE D) : d.pY *ᵥ (d.j0 *ᵥ x) = 0 := by
  rw [Matrix.mulVec_mulVec, d.pY_j0, Matrix.zero_mulVec]

theorem transv_apply {w v : VA V} {u : GA D V} (hu : IsTransv V w v u) (y : VA V) :
    mt V u *ᵥ y = transv V w v y := hu y

variable {w v : VA V} {u : GA D V} {J : Fin ρ} {s : AE D} {c : Fin ρ → AE D}

theorem mem_fixer_of_ne (hu : IsTransv V w v u) (fv : ∀ y : VA V, form V y v = s * (d.pX *ᵥ y) J)
    (fw : ∀ y : VA V, form V y w = c ⬝ᵥ (d.pY *ᵥ y)) {i : Fin ρ} (hiJ : i ≠ J) :
    u ∈ GlobalTheory.MixPer.fixer V (d.jX.submatrix id fun _ : Fin 1 => i) := by
  rw [GlobalTheory.MixPer.mem_fixer]
  ext r k
  rw [mul_apply_col, submatrix_col, transv_fix hu, col_apply]
  · rfl
  · rw [fv, pX_jX_single d, Pi.single_eq_of_ne' hiJ, mul_zero]
  · rw [fw, pY_jX_vec d, dotProduct_zero]

theorem transv_jX (hu : IsTransv V w v u) (fv : ∀ y : VA V, form V y v = s * (d.pX *ᵥ y) J)
    (fw : ∀ y : VA V, form V y w = c ⬝ᵥ (d.pY *ᵥ y)) {x : Fin ρ → AE D} (hw : w = d.jX *ᵥ x) :
    mt V u ⬝ d.jX = d.jX + d.jX ⬝ (s • vecMulVec x (Pi.single J 1)) := by
  ext r k
  rw [mul_apply_col, transv_apply hu, transv, fv, fw, pX_jX_single d, pY_jX_vec d]
  simp only [dotProduct_zero, mul_zero, zero_smul, sub_zero]
  rw [Matrix.add_apply, mul_apply_col, smul_vecMulVec_single, Matrix.mulVec_smul, ← hw]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, col_apply]

theorem unitaryTransvection_on_anisotropic_part (hu : IsTransv V w v u) (fv : ∀ y : VA V, form V y v = s * (d.pX *ᵥ y) J)
    (fw : ∀ y : VA V, form V y w = c ⬝ᵥ (d.pY *ᵥ y)) : mt V u ⬝ d.j0 = d.j0 + d.jX ⬝ (0 : Mx D ρ V₀.rank) := by
  rw [Matrix.mul_zero, add_zero]
  ext r k
  rw [mul_apply_col, transv_fix hu, col_apply]
  · rw [fv, isotropicProjection_anisotropic_vec_eq_zero d, Pi.zero_apply, mul_zero]
  · rw [fw, dualProjection_anisotropic_vec_eq_zero d, dotProduct_zero]

end Mid

end GlobalTheory.TransvMid

open GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction in

theorem GlobalTheory.TransvMid.exists_mid : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (z : Fin V₀.rank → D.host.E) (j : Fin ρ) (a : Fin ρ → D.host.E), a j = 1 → (∀ i, j < i → a i = 0) → j.1 + 1 < ρ → ∀ s : AE D, ∃ v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v = 0 ∧ (∀ i k : Fin ρ, k ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (Pi.single k 1)) v * GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a i = 0) ∧ ∀ u : GA D V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v u → (∀ i : {i : Fin ρ // i ≤ j}, u ∈ fixer V (d.jX.submatrix id fun _ : Fin 1 => i.1)) ∧ simpleSum d z u = s := by
  intro D V V₀ ρ d z j a haj hai hj s
  set J : Fin ρ := ⟨j.1 + 1, hj⟩ with hJ
  have hjJ : j < J := by rw [Fin.lt_def]; simp [hJ]
  have haJ : ratVec a J = 0 := by simp [ratVec, hai J hjJ]
  have hw : vecX d (ratVec a) = d.jX *ᵥ ratVec a := rfl
  refine ⟨d.jY *ᵥ Pi.single J (cA D s), ?_, ?_, ?_⟩
  · rw [GlobalTheory.TransvMid.form_jY_single, hw, Matrix.mulVec_mulVec, d.pX_jX, Matrix.one_mulVec, haJ, mul_zero]
  · intro i k hki
    rw [GlobalTheory.TransvMid.form_jY_single, vecX, Matrix.mulVec_mulVec, d.pX_jX, Matrix.one_mulVec]
    by_cases hk : k = J
    · subst hk
      have : ratVec a i = 0 := by simp [ratVec, hai i (lt_of_lt_of_le hjJ hki)]
      rw [this, mul_zero]
    · rw [Pi.single_eq_of_ne' hk, mul_zero, zero_mul]
  · intro u hu
    have fv : ∀ y : VA V, form V y (d.jY *ᵥ Pi.single J (cA D s)) = s * (d.pX *ᵥ y) J :=
      fun y => GlobalTheory.TransvMid.form_jY_single d y J s
    have fw : ∀ y : VA V, form V y (vecX d (ratVec a)) = (fun k => cA D (ratVec a k)) ⬝ᵥ (d.pY *ᵥ y) :=
      fun y => GlobalTheory.TransvMid.form_jX d y _
    generalize d.jY *ᵥ Pi.single J (cA D s) = v at hu fv
    generalize hwv : vecX d (ratVec a) = w at hu fw
    rw [vecX] at hwv
    refine ⟨fun i => GlobalTheory.TransvMid.mem_fixer_of_ne d hu fv fw (ne_of_lt (lt_of_le_of_lt i.2 hjJ)), ?_⟩
    rw [GlobalTheory.MixPer.simpleSum_eq d z (GlobalTheory.TransvMid.transv_jX d hu fv fw hwv.symm)
      (GlobalTheory.TransvMid.unitaryTransvection_on_anisotropic_part d hu fv fw), GlobalTheory.MixPer.superSum_const]
    simp only [Matrix.zero_mulVec, dotProduct_zero, add_zero, one_mul]
    rw [GlobalTheory.TransvMid.upSum_smul_vecMulVec s _ j J rfl]
    simp [ratVec, haj]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTransvectionFixingIsotropicLastSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.TransvLast

open GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction

variable {D : D7}

theorem form_mulVec (S : HSp D) {k l : ℕ} (M : Mx D S.rank k) (N : Mx D S.rank l) (x : Fin k → AE D)
    (y : Fin l → AE D) :
    form S (M *ᵥ x) (N *ᵥ y) = (fun i => cA D (y i)) ⬝ᵥ ((adj N ⬝ (gA S ⬝ M)) *ᵥ x) := by
  have h : (fun i => cA D ((N *ᵥ y) i)) = N.map (cA D) *ᵥ (fun i => cA D (y i)) :=
    funext fun i => RingHom.map_mulVec (cA D) N y i
  rw [form, h, ← Matrix.vecMul_transpose (N.map (cA D)), ← Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec]
  rfl

theorem conj_smul {n : ℕ} (c : AE D) (y : Fin n → AE D) :
    (fun i => cA D ((c • y) i)) = cA D c • fun i => cA D (y i) := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]

theorem conj_ratV {n : ℕ} (z : Fin n → D.host.E) : (fun i => cA D (ratV z i)) = ratV (star z) :=
  funext fun i => GlobalTheory.DualPairCheck.cA_incA (z i)

theorem ratV_dotProduct {n : ℕ} (x y : Fin n → D.host.E) : ratV x ⬝ᵥ ratV y = incA D (x ⬝ᵥ y) := by
  simp only [dotProduct, map_sum, map_mul]
  rfl

theorem incA_inv_mul {x : D.host.E} (hx : x ≠ 0) : incA D x⁻¹ * incA D x = 1 := by
  rw [← map_mul, inv_mul_cancel₀ hx, map_one]

section Lemmas

variable {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ)

theorem hermSpaceAdelicForm_isotropic_anisotropic_zero (b : Fin ρ → AE D) (y : Fin V₀.rank → AE D) : form V (vecX d b) (d.j0 *ᵥ y) = 0 := by
  rw [vecX, form_mulVec, d.gram_0X, Matrix.zero_mulVec, dotProduct_zero]

theorem form_vecX_vecX (b b' : Fin ρ → AE D) : form V (vecX d b) (vecX d b') = 0 := by
  rw [vecX, vecX, form_mulVec, d.gram_XX, Matrix.zero_mulVec, dotProduct_zero]

theorem hermSpaceAdelicForm_anisotropic_isotropic_zero (y : Fin V₀.rank → AE D) (b : Fin ρ → AE D) : form V (d.j0 *ᵥ y) (vecX d b) = 0 := by
  rw [vecX, form_mulVec, d.wittDecomp_gram_X_anisotropic, Matrix.zero_mulVec, dotProduct_zero]

theorem hermSpaceAdelicForm_anisotropic_rational_smul (z : Fin V₀.rank → D.host.E) (c : AE D) :
    form V (d.j0 *ᵥ ratV z) (d.j0 *ᵥ (c • ratV z)) = cA D c * incA D (star z ⬝ᵥ V₀.gram *ᵥ z) := by
  rw [form_mulVec, d.gram_00, conj_smul, smul_dotProduct, conj_ratV, gA, ← GlobalTheory.MixPer.ratV_mulVec, ratV_dotProduct,
    smul_eq_mul]

theorem mt_jX_of_isTransv {w v : VA V} {u : GA D V} (hu : IsTransv V w v u)
    (hw : ∀ b, form V (vecX d b) w = 0) (hv : ∀ b, form V (vecX d b) v = 0) : mt V u ⬝ d.jX = d.jX := by
  refine Matrix.ext_of_mulVec_single fun i => ?_
  have h : act V u (vecX d (Pi.single i 1)) = transv V w v (vecX d (Pi.single i 1)) := hu _
  rw [transv, hv, hw, zero_smul, zero_smul, mul_zero, zero_smul, add_zero, sub_zero, sub_zero] at h
  rw [← Matrix.mulVec_mulVec]
  exact h

theorem mt_of_isTransv {S : HSp D} {w v y : VA S} {u : GA D S} (hu : IsTransv S w v u) (hy : form S y w = 0) :
    mt S u *ᵥ y = y + form S y v • w := by
  have h : act S u y = transv S w v y := hu _
  rw [transv, hy, zero_smul, mul_zero, zero_smul, sub_zero, sub_zero] at h
  exact h

theorem simpleSum_of {z : Fin V₀.rank → D.host.E} {u : GA D V} {c : Fin ρ → AE D} (s : AE D)
    (hX : mt V u ⬝ d.jX = d.jX) (hy : mt V u *ᵥ (d.j0 *ᵥ ratV z) = d.j0 *ᵥ ratV z + s • (d.jX *ᵥ c)) :
    simpleSum d z u = s * (ell D ρ ⬝ᵥ c) := by
  rw [simpleSum, blockX, hX, d.pX_jX, upSum_one, zero_add, coefX, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hy, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, d.pX_j0,
    d.pX_jX, Matrix.zero_mulVec, Matrix.one_mulVec, zero_add, dotProduct_smul, smul_eq_mul]

theorem mem_fixer_column {u : GA D V} (hX : mt V u ⬝ d.jX = d.jX) (i : Fin ρ) :
    u ∈ fixer V (d.jX.submatrix id fun _ : Fin 1 => i) := by
  rw [mem_fixer]
  ext k l
  have h := congrFun (congrFun hX k) i
  rw [Matrix.mul_apply] at h
  simpa only [Matrix.mul_apply, Matrix.submatrix_apply, id] using h

theorem ell_dotProduct_last {j : Fin ρ} (hj : j.1 + 1 = ρ) {a : Fin ρ → D.host.E} (haj : a j = 1) :
    ell D ρ ⬝ᵥ ratVec a = 1 := by
  rw [dotProduct, Finset.sum_eq_single j]
  · simp [ell, hj, ratVec, haj]
  · intro i _ hij
    have : ¬ (i.1 + 1 = ρ) := fun h => hij (Fin.ext (Nat.add_right_cancel (h.trans hj.symm)))
    simp [ell, this]
  · intro h
    exact absurd (Finset.mem_univ j) h

end Lemmas

theorem exists_transv_simpleSum_last : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (z : Fin V₀.rank → D.host.E), star z ⬝ᵥ V₀.gram *ᵥ z ≠ 0 → ∀ (j : Fin ρ) (a : Fin ρ → D.host.E), a j = 1 → (∀ i, j < i → a i = 0) → j.1 + 1 = ρ → ∀ s : AE D, ∃ v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v = 0 ∧ (∀ i k : Fin ρ, k ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (Pi.single k 1)) v * GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a i = 0) ∧ ∀ u : GA D V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v u → (∀ i : {i : Fin ρ // i ≤ j}, u ∈ fixer V (d.jX.submatrix id fun _ : Fin 1 => i.1)) ∧ simpleSum d z u = s := by
  intro D V V₀ ρ d z hz j a haj _ hj s
  refine ⟨d.j0 *ᵥ (cA D (s * incA D (star z ⬝ᵥ V₀.gram *ᵥ z)⁻¹) • ratV z), hermSpaceAdelicForm_isotropic_anisotropic_zero d _ _,
    fun i k _ => by rw [hermSpaceAdelicForm_isotropic_anisotropic_zero, zero_mul], fun u hu => ?_⟩
  have hX := mt_jX_of_isTransv d hu (fun b => form_vecX_vecX d b _) (fun b => hermSpaceAdelicForm_isotropic_anisotropic_zero d b _)
  have hy := mt_of_isTransv hu (hermSpaceAdelicForm_anisotropic_isotropic_zero d (ratV z) (ratVec a))
  rw [hermSpaceAdelicForm_anisotropic_rational_smul, cA_cA, mul_assoc, incA_inv_mul hz, mul_one] at hy
  exact ⟨fun i => mem_fixer_column d hX i.1, (simpleSum_of d s hX hy).trans (by rw [ell_dotProduct_last hj haj, mul_one])⟩

end GlobalTheory.TransvLast

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsPreserveThetaFunctionsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatThetaMaps_preserve_thetaFunctions : ∀ D : D7, FlatLaw D → ∀ (ψ : AddChar (AF D.host.F) ℂ), (∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) Ψ, IsThetaFunO ψ B.V J.W Ψ → IsThetaFunO ψ B.V₀ J.W₀ (flatBF s Ψ)) ∧ ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) Ψ, IsThetaFunO ψ J.W B.V Ψ → IsThetaFunO ψ J.W₀ B.V₀ (flatFB s Ψ) := by
  first | exact @GlobalTheory.Unf.FlatTheta.flat_isThetaFun | exact GlobalTheory.Unf.FlatTheta.flat_isThetaFun | (intros; apply GlobalTheory.Unf.FlatTheta.flat_isThetaFun <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedLatticeFiniteExpansionsLocalFieldStatement
section
open GlobalTheory.FinPl GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData ValuativeRel IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedLattice_finite_expansions_localField : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (χ : AddChar 𝓀[k] ℂ), χ ≠ 1 → ∀ (Λ : Submodule 𝒪[k] (n → k)) [Λ.IsLattice k], (∀ P : Pair k n', latInd (gluedS q 1 P.ker P.vec) Λ = ((resCard k : ℂ) ^ Fintype.card n)⁻¹ • (tensCol (latInd P.ker Λ) (vecInd Λ) + ∑ Q ∈ withLat Λ, tensCol (latInd P.ker Q.ker + mainDatum q χ 1 P Q) (charInd χ Q)) ∧ latInd P.ker Λ + ∑ Q ∈ withLat Λ, (latInd P.ker Q.ker + mainDatum q χ 1 P Q) = ((resCard k : ℂ) ^ Fintype.card n) • latInd P.lat Λ) ∧ (∀ R : Pair k n', latInd Λ (gluedS q 1 R.ker R.vec) = tensRow (latInd Λ R.ker) (dualInd Λ) + ∑ Q ∈ withLat Λ, tensRow (phiOne Q R) (cosetInd q Q.lat Q.red)) ∧ ∀ (L : Submodule 𝒪[k] (n' → k)) [L.IsLattice k], latInd Λ (lastKer L) = tensRow (latInd Λ L) (dualInd Λ) ∧ latInd Λ (lastPair q L).lat = tensRow (latInd Λ L) (dualInd Λ + ∑ Q ∈ withLat Λ, cosetInd q Q.lat Q.red) := by
  first | exact @GlobalTheory.GluedExp.finite_expansions | exact GlobalTheory.GluedExp.finite_expansions | (intros; apply GlobalTheory.GluedExp.finite_expansions <;> assumption)
end

