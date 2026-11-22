import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0251
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0079
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0176
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0252
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0206
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0239
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommutingEndAlgebrasCommonFixedVector
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory

open NumberField IsDedekindDomain Matrix in
private theorem sum_smulRight_finBasis_mul_smulRight_eq_one {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (w : W) (ℓ : Module.Dual ℂ W) (h : ℓ w = 1) :
    ∑ i, ℓ.smulRight (Module.finBasis ℂ W i) * ((Module.finBasis ℂ W).coord i).smulRight w = 1 := by
  ext x
  simpa [h] using (Module.finBasis ℂ W).sum_repr x

open NumberField IsDedekindDomain Matrix in
private theorem exists_dual_algHom_smulRight_apply_ne_zero {W V : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] [AddCommGroup V] [Module ℂ V] (w : W) (ℓ : Module.Dual ℂ W)
    (h : ℓ w = 1) (Φ : Module.End ℂ W →ₐ[ℂ] Module.End ℂ V) {y : V} (hy : y ≠ 0) :
    ∃ φ : Module.Dual ℂ W, Φ (φ.smulRight w) y ≠ 0 := by
  by_contra! hzero
  apply hy
  calc y = Φ 1 y := by simp
    _ = ∑ i, Φ (ℓ.smulRight (Module.finBasis ℂ W i))
          (Φ (((Module.finBasis ℂ W).coord i).smulRight w) y) := by
        rw [← sum_smulRight_finBasis_mul_smulRight_eq_one w ℓ h, map_sum, LinearMap.sum_apply]
        simp only [map_mul, Module.End.mul_apply]
    _ = 0 := by simp [hzero]

open NumberField IsDedekindDomain Matrix in
private theorem smulRight_mul_smulRight_of_apply_eq_one {W : Type} [AddCommGroup W] [Module ℂ W]
    (w : W) (ℓ φ : Module.Dual ℂ W) (h : ℓ w = 1) :
    ℓ.smulRight w * φ.smulRight w = φ.smulRight w := by
  ext x
  simp [h]

open NumberField IsDedekindDomain Matrix in

theorem _root_.GlobalTheory.commuting_endAlgebras_common_fixed_vector :
    ∀ (ι : Type) [Fintype ι] (Wv : ι → Type) [∀ v, AddCommGroup (Wv v)] [∀ v, Module ℂ (Wv v)]
      [∀ v, FiniteDimensional ℂ (Wv v)] (V : Type) [AddCommGroup V] [Module ℂ V]
      (Φ : ∀ v, Module.End ℂ (Wv v) →ₐ[ℂ] Module.End ℂ V) (w : ∀ v, Wv v)
      (ℓ : ∀ v, Module.Dual ℂ (Wv v)), Nontrivial V → (∀ v, ℓ v (w v) = 1) →
      (∀ u v, u ≠ v → ∀ A B, Commute (Φ u A) (Φ v B)) →
      ∃ y : V, y ≠ 0 ∧ ∀ v, Φ v ((ℓ v).smulRight (w v)) y = y := by
  intro ι _ Wv _ _ _ V _ _ Φ w ℓ _ hℓ hcomm
  classical
  have key : ∀ s : Finset ι, ∃ y : V, y ≠ 0 ∧ ∀ v ∈ s, Φ v ((ℓ v).smulRight (w v)) y = y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨y, hy⟩ := exists_ne (0 : V)
      exact ⟨y, hy, by simp⟩
    | insert v s hv ih =>
      obtain ⟨y, hy0, hy⟩ := ih
      obtain ⟨φ, hφ⟩ := exists_dual_algHom_smulRight_apply_ne_zero (w v) (ℓ v) (hℓ v) (Φ v) hy0
      refine ⟨Φ v (φ.smulRight (w v)) y, hφ, fun u hu => ?_⟩
      rcases Finset.mem_insert.mp hu with rfl | hu
      · rw [← Module.End.mul_apply, ← map_mul,
          smulRight_mul_smulRight_of_apply_eq_one _ _ _ (hℓ u)]
      · have huv : u ≠ v := fun h => hv (h ▸ hu)
        rw [← Module.End.mul_apply, (hcomm u v huv _ _).eq, Module.End.mul_apply, hy u hu]
  obtain ⟨y, hy0, hy⟩ := key Finset.univ
  exact ⟨y, hy0, fun v => hy v (Finset.mem_univ v)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CosetInMvUp
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2

theorem cosetIn_mv_up : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) (j : ℕ), X.Ok → Pr.Ok → (∀ w ∈ QE sel (mu : Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal) → ∀ (q : PtAt R sel mu cst u j) (P : Pr.vT u) (x : Sp X.E (R.N j)), x ∈ q.1.1.deco.1.N → q.1.1.deco.1.f P x = 1 → cosetIn (PtY.mv q (q.1.1.deco.up P (Pr.T u : 𝓞 X.E) x) : PtAt R sel mu cst u j) = cosetIn q := by
  intro X Pr R sel S mu cst u j hX hPr hQ q P x hx hf
  have hP := moveHyp_of_ok hPr u P
  have h := mv_up (Pr.T u) q P hP (T_unif hX hPr u P) (fun w => ne_of_T_notMem hPr u P (hQ w.1 w.2))
    (ysAt_off sel mu cst hPr u hQ j P) hx hf
  have hs := (upN_spec q.1.1.deco.2.lat q.1.1.deco.2.uni P.1 hP.ne hx).2.2.1
  have key : ∀ w : Pr.vGs, (q.1.1.deco.1.up P (Pr.T u : 𝓞 X.E) x).at w.1 = q.1.1.deco.1.at w.1 := fun w =>
    (hs w.1 (hP.sg w).1 (hP.sg w).2).localization_eq
  have hfr : frsF sel mu (PtY.mv q (q.1.1.deco.up P (Pr.T u : 𝓞 X.E) x)).1.1 = frsF sel mu q.1.1 := by
    funext P'
    unfold frsF
    split_ifs with hw
    · show (PtY.mv q (q.1.1.deco.up P (Pr.T u : 𝓞 X.E) x)).1.1.deco.1.liftFr ⟨P'.1, hw⟩ = q.1.1.deco.1.liftFr ⟨P'.1, hw⟩
      rw [h.1]
      unfold Deco.liftFr
      rw [key ⟨P'.1, hw⟩]
      rfl
    · show (PtY.mv q (q.1.1.deco.up P (Pr.T u : 𝓞 X.E) x)).1.1.1.2 _ = q.1.1.1.2 _
      rw [h.2.1]
  funext P'
  unfold cosetIn
  rw [hfr, h.2.2]

end GlobalTheory.Mem.Col2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivariantMapCarriesGelfandInvariantToFunctionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariant_map_carries_gelfandInvariant_to_function : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), IsInfFam θ → ∀ T : MMap M, IsMultMap θ M J χ T → ∀ [DecidableEq D.what₂.Tau] (τ : D.what₂.Tau) (k : ℕ) (v : M.Vec) (w : M.sm τ), (w : M.H τ) = gelfH (gramAt D V τ) (M.rep τ) k (v τ) → gelf θ V τ k (T v) = T (Function.update v τ w) := by
  first | exact @GlobalTheory.MultGelf.gelf_apply | exact GlobalTheory.MultGelf.gelf_apply | (intros; apply GlobalTheory.MultGelf.gelf_apply <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdaptedFrameFamilyLongerFlagGenericLine
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

namespace StepLoc

variable {ι : Type} {m k : ι → ℕ} {K : Type} [Field K] {O : Subring K} {τ : ι}

abbrev blk (k : ι → ℕ) (τ : ι) (P : Mat m K) : Matrix (Rest m k τ) (Rest m k τ) K :=
  (P τ).submatrix Subtype.val Subtype.val

theorem mul_apply_rest {P : Mat m K} (hP : Par k O P) (g : Mat m K) (a : Fin (m τ)) (j : Rest m k τ) :
    (g * P) τ a j.1 = Matrix.vecMul (fun l : Rest m k τ => g τ a l.1) (blk k τ P) j := by
  rw [Pi.mul_apply, Matrix.mul_apply, ← Fintype.sum_subtype_add_sum_subtype (fun l : Fin (m τ) => k τ ≤ (l : ℕ))]
  have : ∑ l : {l : Fin (m τ) // ¬ k τ ≤ (l : ℕ)}, g τ a l.1 * P τ l.1 j.1 = 0 :=
    Finset.sum_eq_zero fun l _ => by
      have h1 := l.2
      have h2 := j.2
      rw [(hP τ).2.2.2 l.1 j.1 (by omega) (by show (l.1 : ℕ) < j.1; omega), mul_zero]
  rw [this, add_zero]
  rfl

theorem blk_mul_inv {P : Mat m K} (hP : Par k O P) : blk k τ P * blk k τ P⁻¹ = 1 := by
  ext a j
  have := mul_apply_rest hP.inv P a.1 j
  rw [Mat.mul_inv hP.det_ne] at this
  refine this.symm.trans ?_
  show (1 : Matrix _ _ K) a.1 j.1 = _
  simp only [Matrix.one_apply, Subtype.ext_iff]

theorem line_iff {Q : Mat m K} (hQ : Par k O Q) (hk : k τ < m τ) {s : Rest m k τ → K} {b : K}
    (hs : ∀ j : Rest m k τ, s j = b * Q τ ⟨k τ, hk⟩ j.1) (hb : b ≠ 0) (g : Mat m K) :
    (∃ a : K, ∀ j : Rest m k τ, (g * Q) τ ⟨k τ, hk⟩ j.1 = a * s j) ↔
      ∀ j : Fin (m τ), k τ < j → g τ ⟨k τ, hk⟩ j = 0 := by
  have e : ∀ (x : K) (j : Rest m k τ), Matrix.vecMul (Pi.single (⟨⟨k τ, hk⟩, le_rfl⟩ : Rest m k τ) x) (blk k τ Q) j
      = x * Q τ ⟨k τ, hk⟩ j.1 := fun x j => by
    rw [Matrix.single_vecMul]
    simp
  constructor
  · rintro ⟨a, ha⟩ j hj
    have h1 : Matrix.vecMul (fun l : Rest m k τ => g τ ⟨k τ, hk⟩ l.1) (blk k τ Q) =
        Matrix.vecMul (Pi.single (⟨⟨k τ, hk⟩, le_rfl⟩ : Rest m k τ) (a * b)) (blk k τ Q) := by
      funext l
      rw [← mul_apply_rest hQ, ha, e, hs, mul_assoc]
    have h2 := congrArg (Matrix.vecMul · (blk k τ Q⁻¹)) h1
    simp only [Matrix.vecMul_vecMul, blk_mul_inv hQ, Matrix.vecMul_one] at h2
    have h3 := congrFun h2 ⟨j, hj.le⟩
    rwa [Pi.single_eq_of_ne (fun h => hj.ne' (congrArg (fun x : Rest m k τ => (x.1 : ℕ)) h))] at h3
  · intro h
    refine ⟨g τ ⟨k τ, hk⟩ ⟨k τ, hk⟩ / b, fun j => ?_⟩
    have h1 : (fun l : Rest m k τ => g τ ⟨k τ, hk⟩ l.1) =
        Pi.single (⟨⟨k τ, hk⟩, le_rfl⟩ : Rest m k τ) (g τ ⟨k τ, hk⟩ ⟨k τ, hk⟩) := by
      funext l
      by_cases hl : l = ⟨⟨k τ, hk⟩, le_rfl⟩
      · rw [hl, Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hl]
        exact h _ (lt_of_le_of_ne l.2 fun h' => hl (Subtype.ext (Fin.ext h'.symm)))
    rw [mul_apply_rest hQ, h1, e, hs, ← mul_assoc, div_mul_cancel₀ _ hb]

theorem par_succ_iff {k' : ι → ℕ} (hk : k τ < m τ) (h1 : k' τ = k τ + 1) (h2 : ∀ τ', τ' ≠ τ → k' τ' = k τ')
    (g : Mat m K) :
    Par k' O g ↔ Par k O g ∧ ∀ j : Fin (m τ), k τ < j → g τ ⟨k τ, hk⟩ j = 0 := by
  constructor
  · intro h
    refine ⟨h.mono (fun t => ?_) le_rfl, fun j hj => (h τ).2.2.2 _ j (by rw [h1]; exact Nat.lt_succ_self _) hj⟩
    by_cases ht : t = τ
    · rw [ht, h1]; exact Nat.le_succ _
    · exact (h2 t ht).ge
  · rintro ⟨h, h'⟩ t
    refine ⟨(h t).1, (h t).2.1, (h t).2.2.1, fun i j hi hij => ?_⟩
    by_cases ht : t = τ
    · subst ht
      rw [h1] at hi
      rcases (Nat.lt_succ_iff.1 hi).lt_or_eq with hi | hi
      · exact (h t).2.2.2 i j hi hij
      · obtain rfl : i = ⟨k t, hk⟩ := Fin.ext hi
        exact h' j hij
    · exact (h t).2.2.2 i j (h2 t ht ▸ hi) hij

theorem exists_completion (hk : k τ < m τ) (c : Rest m k τ → K) (i : Rest m k τ) (hi : c i = 1) :
    ∃ N : Mat m K, (∀ j : Rest m k τ, N τ ⟨k τ, hk⟩ j.1 = c j) ∧
      ∀ O : Subring K, (∀ j, c j ∈ O) → Par k O N := by
  classical
  let v : Fin (m τ) → K := fun j => if h : k τ ≤ (j : ℕ) then c ⟨j, h⟩ else 0
  have hv : ∀ j : Rest m k τ, v j.1 = c j := fun j => dif_pos j.2
  let T : Matrix (Fin (m τ)) (Fin (m τ)) K :=
    ((1 : Matrix _ _ K).updateRow i.1 v).submatrix (Equiv.swap ⟨k τ, hk⟩ i.1) id
  have hd : T.det * T.det = 1 := by
    have e : ((1 : Matrix _ _ K).updateRow i.1 v).det = 1 := by
      rw [← Matrix.cramer_transpose_apply, Matrix.transpose_one, Matrix.cramer_one]
      exact (hv i).trans hi
    rw [Matrix.det_permute, e, mul_one, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  refine ⟨Function.update (1 : Mat m K) τ T, fun j => ?_, fun O hO t => ?_⟩
  · rw [Function.update_self]
    show ((1 : Matrix _ _ K).updateRow i.1 v) (Equiv.swap ⟨k τ, hk⟩ i.1 ⟨k τ, hk⟩) j.1 = _
    rw [Equiv.swap_apply_left, Matrix.updateRow_self, hv]
  by_cases ht : t = τ
  · subst ht
    rw [Function.update_self]
    have hm : ∀ a b, T a b ∈ O := fun a b => by
      show ((1 : Matrix _ _ K).updateRow i.1 v) _ b ∈ O
      rw [Matrix.updateRow_apply]
      split_ifs
      · show dite _ _ _ ∈ O
        split_ifs
        exacts [hO _, O.zero_mem]
      · rw [Matrix.one_apply]; split_ifs; exacts [O.one_mem, O.zero_mem]
    refine ⟨hm, left_ne_zero_of_mul_eq_one hd, ?_, fun a b ha hab => ?_⟩
    · rw [← eq_inv_of_mul_eq_one_left hd]; exact det_mem hm
    · have h1 : a ≠ ⟨k t, hk⟩ := fun h => ha.ne (congrArg Fin.val h)
      have h2 : a ≠ i.1 := fun h => (h ▸ ha).not_ge i.2
      show ((1 : Matrix _ _ K).updateRow i.1 v) (Equiv.swap ⟨k t, hk⟩ i.1 a) b = 0
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Matrix.updateRow_ne h2, Matrix.one_apply_ne hab.ne]
  · rw [Function.update_of_ne ht]
    exact Par.one t

end StepLoc

open StepLoc in

theorem exists_fr_stepSet (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (ι : Type) [Finite ι]
    (m k k' : ι → ℕ) (S : Fr M m k) (τ : ι) (hk : k τ < m τ) (A₀ : Mat m Ω) (EE : M.Lat (Rest m k τ))
    (s : Rest m k τ → Ω') (h1 : k' τ = k τ + 1) (h2 : ∀ τ', τ' ≠ τ → k' τ' = k τ')
    (hA₀ : A₀ ∈ S.S (genericPoint M.Z))
    (hE : ∀ z, ∀ A ∈ S.S z, (dualBlock k τ A₀ A).det ≠ 0 ∧
      EE.E z = Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A)))
    (hP : ProjPoints M EE M' φ f s) :
    ∃ S' : Fr M' m k', ∀ z', S'.S z' = stepSet S τ hk A₀ M' φ f s z' := by
  refine ⟨⟨stepSet S τ hk A₀ M' φ f s, fun z' => ?_⟩, fun _ => rfl⟩
  obtain ⟨U, A, hz, hA, hU⟩ := S.loc (f z')
  have hAU : ∀ w ∈ U, A ∈ S.S w := fun w hw => (hU w hw A).2 (by rw [Mat.mul_inv hA]; exact Par.one)
  obtain ⟨hd, hE'⟩ := hE _ A (hAU _ hz)
  obtain ⟨i, hi⟩ := hP.cover z' _ hd hE'
  set c := ((dualBlock k τ A₀ A).map φ).mulVec s with hc
  let ψ : Ω →+* Ω' := φ
  obtain ⟨N, hN, hNO⟩ := exists_completion hk (fun j => c j / c i) i (div_self hi.1)
  have hAφ : ∀ t, (A.map ψ t).det ≠ 0 := fun t => by rw [Mat.det_map]; exact (map_ne_zero ψ).2 (hA t)
  have hN0 : Par k ⊤ N := hNO ⊤ fun _ => trivial
  have hP0 : Par k ⊤ ((A * A₀⁻¹).map ψ) :=
    ((Fr.mem_iff hA₀).1 (Fr.mem_genericPoint (hAU _ hz))).map ψ fun _ _ => trivial
  have hs : s = Matrix.vecMul c (blk k τ ((A * A₀⁻¹).map ψ)) := by
    have hP1 := (Fr.mem_iff hA₀).1 (Fr.mem_genericPoint (hAU _ hz))
    have e1 : (blk k τ (A * A₀⁻¹))⁻¹ * blk k τ (A * A₀⁻¹) = 1 :=
      Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_right_inverse (blk_mul_inv hP1))
    have e2 : c = Matrix.vecMul s ((blk k τ (A * A₀⁻¹))⁻¹.map ψ) := by
      rw [hc, ← Matrix.mulVec_transpose]
      rfl
    have e3 : blk k τ ((A * A₀⁻¹).map ψ) = (blk k τ (A * A₀⁻¹)).map ψ := rfl
    rw [e2, e3, Matrix.vecMul_vecMul, ← Matrix.map_mul, e1, Matrix.map_one _ ψ.map_zero ψ.map_one,
      Matrix.vecMul_one]
  have hQ : ∀ j : Rest m k τ, s j = c i * (N * (A * A₀⁻¹).map ψ) τ ⟨k τ, hk⟩ j.1 := fun j => by
    have e : (fun l : Rest m k τ => N τ ⟨k τ, hk⟩ l.1) = (c i)⁻¹ • c := by
      funext l
      rw [hN, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
    rw [mul_apply_rest hP0, e, Matrix.smul_vecMul, ← hs, Pi.smul_apply, smul_eq_mul, mul_inv_cancel_left₀ hi.1]
  have hA₁ : ∀ t, ((N * A.map ψ) t).det ≠ 0 := fun t => by
    rw [Pi.mul_apply, Matrix.det_mul]; exact mul_ne_zero (hN0.det_ne t) (hAφ t)
  refine ⟨f ⁻¹ᵁ U ⊓ ⟨_, M'.isOpen_setOf_div c i⟩, N * A.map ψ, ⟨hz, hi⟩, hA₁, fun w hw A' => ?_⟩
  have hNw : Par k (M'.O w).toSubring N := hNO _ hw.2.2
  have hAw : A ∈ S.S (f w) := hAU _ hw.1
  rw [par_succ_iff hk h1 h2, ← line_iff (hN0.mul hP0) hk hQ hi.1]
  have e1 : A' * (N * A.map ψ)⁻¹ * (N * (A * A₀⁻¹).map ψ) = A' * (A₀.map ψ)⁻¹ := by
    rw [Mat.map_mul, Mat.map_inv, ← mul_assoc N, mul_assoc A', ← mul_assoc _ (N * A.map ψ), Mat.inv_mul hA₁,
      one_mul]
  rw [e1]
  refine and_congr_left' ⟨fun h => ?_, fun h B hB => ?_⟩
  · have := (h A hAw).mul hNw.inv
    rwa [Mat.mul_inv_rev, ← mul_assoc]
  · have h3 : Par k (M'.O w).toSubring ((A * B⁻¹).map ψ) :=
      ((Fr.mem_iff hB).1 hAw).map ψ fun _ hx => hP.hom.map_mem_O hx
    have := h.mul (hNw.mul h3)
    rw [Mat.map_mul, Mat.map_inv, ← mul_assoc N, mul_assoc A', ← mul_assoc _ (N * A.map ψ), Mat.inv_mul hA₁,
      one_mul] at this
    exact this

end GlobalTheory.FlagBundle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgHomEndomorphismOfSpanIntertwiners
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.FinPart

open scoped MonoidAlgebra

theorem exists_algHom_end_of_span_intertwiners :
    ∀ (H W V : Type) [Group H] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ H W) (ρ : Representation ℂ H V),
      σ.IsIrreducible → (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) = ⊤ →
      ∃ Φ : Module.End ℂ W →ₐ[ℂ] Module.End ℂ V, (∀ h, Φ (σ h) = ρ h) ∧
        ∀ T : Module.End ℂ V, (∀ h, Commute T (ρ h)) → ∀ A, Commute T (Φ A) := by
  intro H W V _ _ _ _ _ _ σ ρ hirr hspan
  classical

  have hsurj : Function.Surjective σ.asAlgebraHom := by
    have hB := GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible H W σ hirr
    have hle : Submodule.span ℂ (Set.range σ) ≤ Subalgebra.toSubmodule σ.asAlgebraHom.range := by
      rw [Submodule.span_le]
      rintro _ ⟨h, rfl⟩
      exact ⟨MonoidAlgebra.single h 1, by simp [Representation.asAlgebraHom_single]⟩
    intro A
    have : A ∈ Subalgebra.toSubmodule σ.asAlgebraHom.range := hle (hB ▸ Submodule.mem_top)
    exact this

  have hint : ∀ (f : σ.IntertwiningMap ρ) (a : MonoidAlgebra ℂ H) (w : W),
      ρ.asAlgebraHom a (f.toLinearMap w) = f.toLinearMap (σ.asAlgebraHom a w) := by
    intro f a w
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hx, hy, map_add]
    | single g c =>
      simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply, map_smul]
      congr 1
      exact (Representation.IntertwiningMap.isIntertwining σ ρ f g w).symm
  have hker : RingHom.ker σ.asAlgebraHom ≤ RingHom.ker ρ.asAlgebraHom := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    have hle : (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) ≤
        LinearMap.ker (ρ.asAlgebraHom a) := by
      refine iSup_le fun f => ?_
      rintro _ ⟨w, rfl⟩
      rw [LinearMap.mem_ker, hint, ha]
      simp
    rw [hspan, top_le_iff] at hle
    exact LinearMap.ker_eq_top.1 hle
  let Φ : Module.End ℂ W →ₐ[ℂ] Module.End ℂ V :=
    (Ideal.Quotient.liftₐ (RingHom.ker σ.asAlgebraHom) ρ.asAlgebraHom hker).comp
      (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm.toAlgHom
  have hΦ : ∀ a, Φ (σ.asAlgebraHom a) = ρ.asAlgebraHom a := by
    intro a
    have : (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm (σ.asAlgebraHom a) =
        Ideal.Quotient.mk _ a := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    change Ideal.Quotient.liftₐ _ _ hker ((Ideal.quotientKerAlgEquivOfSurjective hsurj).symm (σ.asAlgebraHom a)) = _
    rw [this]
    rfl
  refine ⟨Φ, fun h => ?_, fun T hT A => ?_⟩
  · have := hΦ (MonoidAlgebra.single h 1)
    simpa [Representation.asAlgebraHom_single] using this
  · obtain ⟨a, rfl⟩ := hsurj A
    rw [hΦ]
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add]; exact hx.add_right hy
    | single g c =>
      rw [Representation.asAlgebraHom_single]
      exact (hT g).smul_right c

end GlobalTheory.FinPart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnHighestWeightPolynomialMapStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_column_highest_weight_polynomial_map : ∀ (ι : Type) [Fintype ι] (m n : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] (U : Submodule ℂ (X →ₗ[ℂ] Pol ι m n)), U ≠ ⊥ → (∀ Φ ∈ U, ∀ τ g, colSub m τ g ∘ₗ Φ ∈ U) → ∃ Φ ∈ U, Φ ≠ 0 ∧ (∀ τ k l, k < l → colLie m τ k l ∘ₗ Φ = 0) ∧ ∃ μ : ι → Fin n → ℤ, ∀ τ k, colLie m τ k k ∘ₗ Φ = (μ τ k : ℂ) • Φ := by
  first | exact @GlobalTheory.DefLift.exists_colHighest | exact GlobalTheory.DefLift.exists_colHighest | (intros; apply GlobalTheory.DefLift.exists_colHighest <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeDualBasisQuotientFrameBlock
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

noncomputable section

namespace GlobalTheory.FlagBundle.QuotDual

variable {ι : Type} {m k : ι → ℕ} {K : Type} [Field K]

abbrev restBlock (k : ι → ℕ) (τ : ι) (g : Mat m K) : Matrix (Rest m k τ) (Rest m k τ) K :=
  (g τ).submatrix Subtype.val Subtype.val

theorem restBlock_mul {O : Subring K} (τ : ι) (g : Mat m K) {h : Mat m K} (hh : Par k O h) :
    restBlock k τ (g * h) = restBlock k τ g * restBlock k τ h := by
  ext i j
  simp only [Matrix.submatrix_apply, Pi.mul_apply, Matrix.mul_apply]
  rw [← Finset.sum_subtype (Finset.univ.filter fun l : Fin (m τ) => k τ ≤ (l : ℕ)) (by simp)
    (fun l => g τ i.1 l * h τ l j.1)]
  refine (Finset.sum_subset (Finset.filter_subset _ _) fun l _ hl => ?_).symm
  have hl' : (l : ℕ) < k τ := by simpa using hl
  have hj := j.2
  rw [(hh τ).2.2.2 l j.1 hl' (by show (l : ℕ) < j.1; omega), mul_zero]

theorem restBlock_one (τ : ι) : restBlock k τ (1 : Mat m K) = 1 :=
  Matrix.submatrix_one _ Subtype.val_injective

theorem restBlock_inv_mul {O : Subring K} (τ : ι) {g : Mat m K} (hg : Par k O g) :
    restBlock k τ g⁻¹ * restBlock k τ g = 1 := by
  rw [← restBlock_mul τ _ hg, Mat.inv_mul hg.det_ne, restBlock_one]

theorem restBlock_inv {O : Subring K} (τ : ι) {g : Mat m K} (hg : Par k O g) :
    (restBlock k τ g)⁻¹ = restBlock k τ g⁻¹ :=
  Matrix.inv_eq_left_inv (restBlock_inv_mul τ hg)

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]

theorem span_mul_le {J : Type} [Fintype J] (O : Subalgebra F Ω) (P B : Matrix J J Ω) (hP : ∀ i j, P i j ∈ O) :
    Submodule.span O (Set.range (P * B)) ≤ Submodule.span O (Set.range B) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun l => ⟨P i l, hP i l⟩, ?_⟩
  ext j
  simp [Matrix.mul_apply, Finset.sum_apply, Subalgebra.smul_def]

variable {M : RatModel F Ω} {S : Fr M m k} {A₀ : Mat m Ω}

theorem par_generic (h₀ : A₀ ∈ S.S (genericPoint M.Z)) {z : M.Z} {A : Mat m Ω} (hA : A ∈ S.S z) :
    Par k (M.O (genericPoint M.Z)).toSubring (A * A₀⁻¹) :=
  (Fr.mem_iff h₀).1 (Fr.mem_genericPoint hA)

theorem det_dualBlock_ne (τ : ι) (h₀ : A₀ ∈ S.S (genericPoint M.Z)) {z : M.Z} {A : Mat m Ω} (hA : A ∈ S.S z) :
    (dualBlock k τ A₀ A).det ≠ 0 := by
  have h := par_generic h₀ hA
  have e := congrArg Matrix.det (restBlock_inv_mul τ h)
  rw [Matrix.det_mul, Matrix.det_one] at e
  show ((restBlock k τ (A * A₀⁻¹))⁻¹).transpose.det ≠ 0
  rw [Matrix.det_transpose, restBlock_inv τ h]
  exact left_ne_zero_of_mul_eq_one e

theorem span_dualBlock_le (τ : ι) (h₀ : A₀ ∈ S.S (genericPoint M.Z)) {z : M.Z} {A A' : Mat m Ω} (hA : A ∈ S.S z)
    (hA' : A' ∈ S.S z) : Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A')) ≤
      Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A)) := by
  have hg := (Fr.mem_iff hA).1 hA'
  have e : A' * A₀⁻¹ = (A' * A⁻¹) * (A * A₀⁻¹) := by
    rw [← mul_assoc, mul_assoc A', Mat.inv_mul (Fr.det_ne hA), mul_one]
  have e2 : dualBlock k τ A₀ A' = (restBlock k τ (A' * A⁻¹)⁻¹).transpose * dualBlock k τ A₀ A := by
    show ((restBlock k τ (A' * A₀⁻¹))⁻¹).transpose = _ * ((restBlock k τ (A * A₀⁻¹))⁻¹).transpose
    rw [e, restBlock_mul τ _ (par_generic h₀ hA), Matrix.mul_inv_rev, Matrix.transpose_mul, restBlock_inv τ hg]
  rw [e2]
  exact span_mul_le _ _ _ fun i j => (hg.inv τ).1 _ _

theorem span_dualBlock_eq (τ : ι) (h₀ : A₀ ∈ S.S (genericPoint M.Z)) {z : M.Z} {A A' : Mat m Ω} (hA : A ∈ S.S z)
    (hA' : A' ∈ S.S z) : Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A')) =
      Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A)) :=
  le_antisymm (span_dualBlock_le τ h₀ hA hA') (span_dualBlock_le τ h₀ hA' hA)

theorem exists_lat_dualBlock (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (ι : Type)
    (m k : ι → ℕ) (S : Fr M m k) (τ : ι) (A₀ : Mat m Ω) (h₀ : A₀ ∈ S.S (genericPoint M.Z)) :
    ∃ EE : M.Lat (Rest m k τ), ∀ z, ∀ A ∈ S.S z, (dualBlock k τ A₀ A).det ≠ 0 ∧
      EE.E z = Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A)) := by
  refine ⟨⟨fun z => Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ (S.nonempty z).some)), fun z => ?_⟩,
    fun z A hA => ⟨det_dualBlock_ne τ h₀ hA, span_dualBlock_eq τ h₀ hA (S.nonempty z).some_mem⟩⟩
  obtain ⟨U, A, hz, hA, hU⟩ := S.loc z
  have hm : ∀ z' ∈ U, A ∈ S.S z' := fun z' hz' => (hU z' hz' A).2 (by rw [Mat.mul_inv hA]; exact Par.one)
  exact ⟨U, dualBlock k τ A₀ A, hz, det_dualBlock_ne τ h₀ (hm z hz),
    fun z' hz' => span_dualBlock_eq τ h₀ (hm z' hz') (S.nonempty z').some_mem⟩

end GlobalTheory.FlagBundle.QuotDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSubsingletonCohTwistTensLbPowStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_subsingleton_coh_twist_tens_lbPow' : ∀ (k : Type) [Field k] {Y : Scheme.{0}} (f : Y ⟶ Sp k), IsProjOver f → ∀ (A N : LB Y), IsAmpleLB A → N.IsLB → ∀ (G : Y.Modules) [IsFiniteQC G] (B : ℕ), ∃ j₁ : ℕ, ∀ j m : ℕ, j₁ ≤ j → m < B → ∀ p, 0 < p → Subsingleton (coh (twist G (tens (lbPow A j) (lbPow N m))) p) := by
  first | exact @GlobalTheory.exists_subsingleton_coh_twist_tens_lbPow | exact GlobalTheory.exists_subsingleton_coh_twist_tens_lbPow | (intros; apply GlobalTheory.exists_subsingleton_coh_twist_tens_lbPow <;> assumption)
end

