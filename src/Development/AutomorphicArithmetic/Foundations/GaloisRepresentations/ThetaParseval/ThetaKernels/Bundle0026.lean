import Development.AutomorphicArithmetic.AdelicQuotients.WeilRepresentationSmoothVectors
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0010
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0024
import Development.AutomorphicArithmetic.AdelicQuotients.Bundle0012
import Development.AutomorphicArithmetic.AdelicQuotients.Bundle0013
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0020
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0013
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0521
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0019
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0002
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.WeilBound.ThetaLifts.FrameEstimates.CuspRapid
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1887
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1688
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0021

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsNhdsOneWeilFixesPureTensor
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
open UpperTheory.TP
section Left
open PositivityTheory.ThKEst PositivityTheory.ThKEst.levelStructure PositivityTheory.ThKEst.LatticeQuotientMeasure PositivityTheory.ThKF0.Grow PositivityTheory.ThKF0.Grow.Fi
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
private theorem schr_left_pk {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    {g : (Fin n × Fin d → Af F) → ℂ} (hg : g ∈ SB _) {C : Set (Ten F E n d)} (hC : IsCompact C) :
    ∀ᶠ u in 𝓝 (1 : UA σ X.J), levelStructure.IsFin u → ∀ z : Ten F E n d, (∃ c ∈ C, At (evI F) (z - c)) → ∀ f,
      schr ψ (M.co.e (mat u * z)) (pureA F f g) = schr ψ (M.co.e z) (pureA F f g) := by
  have := ring_AE F E
  have : IsModuleTopology (AF F) (Ten F E n d) := inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
  have he : Continuous M.co.e := IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap
  have hV := schr_near hψ hg (hC.image he)
  have hm : Continuous fun p : UA σ X.J × Ten F E n d => M.co.e ((mat p.1 - 1) * p.2) :=
    he.comp ((((Units.continuous_val.comp continuous_subtype_val).comp continuous_fst).sub continuous_const).matrix_mul
      continuous_snd)
  have h1 := hC.eventually_forall_of_forall_eventually (x₀ := (1 : UA σ X.J))
    (P := fun u c => M.co.e ((mat u - 1) * c) ∈ _) fun c _ => hm.continuousAt.preimage_mem_nhds (by
      rwa [show mat (1 : UA σ X.J) = 1 from rfl, sub_self, Matrix.zero_mul, map_zero])
  filter_upwards [h1] with u h1 hu z hz f
  obtain ⟨c, hc, hz⟩ := hz
  rw [at_iff, smul_sub, sub_eq_zero] at hz
  have hu' : e0 F • (mat u - 1) = mat u - 1 := hu
  have e : mat u * z = z + (mat u - 1) * c := by
    have e1 : (mat u - 1) * c = (mat u - 1) * z := by
      rw [← hu', Matrix.smul_mul, ← Matrix.mul_smul, ← hz, Matrix.mul_smul, Matrix.smul_mul]
    rw [e1, Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]
  rw [e, map_add]
  exact h1 c hc (by rw [← map_smul, ← Matrix.smul_mul, hu']) _ ⟨c, hc, rfl⟩ _ (by rw [← map_smul, ← map_smul, hz]) f
end Left
theorem UpperTheory.exists_nhds_one_weil_fixes_pure_tensor :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), ∀ r s r' s', _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ φ ∈ SB (Fin n × Fin d → Af F), ∃ U ∈ 𝓝 (1 : UA σ X.J), ∀ u ∈ U, (∀ w, (mat u).map (piInf (B.emb w)) = 1) → ∀ f : SInf F (Fin n × Fin d), om (u, 1) (pureA F f φ) = pureA F f φ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp φ hφ
  by_cases h0 : ∀ f : SInf F (Fin n × Fin d), pureA F f φ = 0
  · exact ⟨Set.univ, univ_mem, fun u _ _ f => by rw [h0, map_zero]⟩
  push Not at h0
  obtain ⟨f₀, h0⟩ := h0
  obtain ⟨y, hy⟩ := Function.ne_iff.1 h0
  have hy : pureA F f₀ φ y ≠ 0 := hy
  have hs := IsUWeilPair.isUSplitting hp.weil
  have mem : ∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ schA F (Fin n × Fin d) := fun f =>
    Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  obtain ⟨μ, hμ, -⟩ := PositivityTheory.ThKEst.ParityOfCoefficients.exists_haar (F := F) (κ := Fin n × Fin d)
  obtain ⟨p, C, -, hCc, hb⟩ := _root_.PositivityTheory.ThKEst.coefBd_of_k PositivityTheory.ThKEst.coefReal_of F E σ B n d X W M χX χW om r s r' s' hp μ hμ φ hφ φ hφ 0
  have h1 := schr_left_pk M hp.base.std hφ hCc
  have := PositivityTheory.ThKEst.LatticeQuotientMeasure.ring_AE F E
  have hi : Continuous fun u : UA σ X.J => u⁻¹ :=
    ((continuous_inv (G := GL (Fin n) (AE F E))).comp continuous_subtype_val).subtype_mk fun u => (u⁻¹).2
  have h2 := (hi.tendsto' 1 1 inv_one).eventually h1
  have hc : Continuous fun u : UA σ X.J => ‖om (u, 1) (pureA F f₀ φ) y / pureA F f₀ φ y - 1‖ :=
    ((((hs.cont _ (PositivityTheory.ThKEst.levelStructure.ev_adm y) _ (mem f₀)).comp (continuous_id.prodMk continuous_const)).div_const _).sub
      continuous_const).norm
  have h3 := PositivityTheory.ThKEst.levelStructure.pow_near _ ((isOpen_lt hc (continuous_const (y := (1 / 2 : ℝ)))).mem_nhds (by
    change ‖om 1 (pureA F f₀ φ) y / pureA F f₀ φ y - 1‖ < 1 / 2
    rw [map_one, Module.End.one_apply, div_self hy]
    norm_num))
  refine ⟨_, h1.and (h2.and h3), fun u ⟨h1, h2, h3⟩ hu => ?_⟩
  have hu := PositivityTheory.ThKEst.levelStructure.isFin_of hp.base.cm B.emb hu
  have key : ∀ (f : SInf F (Fin n × Fin d)) x, om (u, 1) (pureA F f φ) x * (starRingEnd ℂ) (om (u, 1) (pureA F f₀ φ) y) =
      pureA F f φ x * (starRingEnd ℂ) (pureA F f₀ φ y) := by
    intro f x
    refine PositivityTheory.ThKEst.fourierInj_of F _ B.ψ hp.base.std μ hμ _ (hs.pres _ _ (mem f)) _ (hs.pres _ _ (mem f₀)) _ (mem f) _ (mem f₀) ?_ x y
    funext w
    obtain ⟨z, rfl⟩ := M.co.e.surjective w
    rw [_root_.PositivityTheory.ThKEst.coefEq_of_k F E σ B n d X W M χX χW om r s r' s' hp μ hμ _ (mem f) _ (mem f₀), PositivityTheory.ThKEst.ParityOfCoefficients.mat_one_inv,
      Matrix.transpose_one, Matrix.mul_one]
    by_cases a : ∃ c ∈ C, At (evI F) (z - c)
    · unfold PositivityTheory.ThKEst.coef
      rw [h2 hu.inv z a]
    by_cases a' : ∃ c ∈ C, At (evI F) (mat u⁻¹ * z - c)
    · unfold PositivityTheory.ThKEst.coef
      rw [← h1 hu _ a', ← Matrix.mul_assoc, show mat u * mat u⁻¹ = 1 from Units.mul_inv u.1, Matrix.one_mul]
    have b := hb f f₀ z
    have b' := hb f f₀ (mat u⁻¹ * z)
    rw [PositivityTheory.ThKEst.maj, if_neg a, mul_zero, norm_le_zero_iff] at b
    rw [PositivityTheory.ThKEst.maj, if_neg a', mul_zero, norm_le_zero_iff] at b'
    rw [b, b']
  have h4 : (starRingEnd ℂ) (om (u, 1) (pureA F f₀ φ) y) ≠ 0 := fun h => by
    have := key f₀ y
    rw [h, mul_zero, eq_comm, mul_eq_zero, map_eq_zero, or_self] at this
    exact hy this
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ f : SInf F (Fin n × Fin d), om (u, 1) (pureA F f φ) = c • pureA F f φ :=
    ⟨(starRingEnd ℂ) (pureA F f₀ φ y) / (starRingEnd ℂ) (om (u, 1) (pureA F f₀ φ) y), fun f => funext fun x => by
      rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff h4, key, mul_comm]⟩
  have h5 : ∀ k : ℕ, om (u ^ k, 1) (pureA F f₀ φ) = c ^ k • pureA F f₀ φ := fun k => by
    induction k with
    | zero => rw [pow_zero, pow_zero, one_smul]; exact congrArg (· (pureA F f₀ φ)) (map_one om)
    | succ k ih =>
      rw [pow_succ, show ((u ^ k * u, 1) : UA σ X.J × UA σ W.J) = (u ^ k, 1) * (u, 1) from by simp, map_mul,
        Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ']
  have h6 : c = 1 := PositivityTheory.ThKH.Locrep.eq_one_of_pow_near fun k => by
    have := h3 hu k
    rwa [Set.mem_ofPred_eq, h5, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hy, mul_one] at this
  intro f
  rw [hc, h6, one_smul]
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsWeilLatticeDatum
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped Matrix
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels UpperTheory.TP.BA
namespace UpperTheory.LatD
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} {v : Pl F}
private theorem at_self_pk {M : Type} [AddCommGroup M] [Module (AF F) M] {x : M} (hx : At (evFin F v) x) :
    sg v 1 • x = x := by
  have h1 := hx (1 - sg v 1) (by rw [map_sub, map_one, PositivityTheory.ThKH.Iwas.ev_sg, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  exact h1.symm
private theorem at_mulA_pk {a : AF F} (ha : At (evFin F v) a) (a' : AF F) : At (evFin F v) (a * a') := fun u hu => by
  have h := ha u hu
  rw [smul_eq_mul] at h ⊢
  rw [← mul_assoc, h, zero_mul]
private theorem sg_one_int_pk : evFin F v (sg v 1) ∈ v.adicCompletionIntegers F := by
  rw [PositivityTheory.ThKH.Iwas.ev_sg]; exact one_mem _
private theorem oh_gen_pk {a : AF F} (h1 : At (evFin F v) a) (h2 : evFin F v a ∈ v.adicCompletionIntegers F) (o : 𝓞 E) :
    a • inclR (F := F) (AF F) (o : E) ∈ Oh E v :=
  AddSubgroup.subset_closure ⟨a, h1, h2, o, rfl⟩
private theorem oh_ind_pk {p : AE F E → Prop}
    (gen : ∀ a : AF F, At (evFin F v) a → evFin F v a ∈ v.adicCompletionIntegers F → ∀ o : 𝓞 E, p (a • inclR (F := F) (AF F) (o : E)))
    (zero : p 0) (add : ∀ x y, p x → p y → p (x + y)) (neg : ∀ x, p x → p (-x)) {x : AE F E} (hx : x ∈ Oh E v) : p x := by
  refine AddSubgroup.closure_induction (p := fun x _ => p x) ?_ zero (fun x y _ _ h h' => add x y h h') (fun x _ h => neg x h) hx
  rintro _ ⟨a, h1, h2, o, rfl⟩
  exact gen a h1 h2 o
private theorem oh_mul_pk {x y : AE F E} (hx : x ∈ Oh E v) (hy : y ∈ Oh E v) : x * y ∈ Oh E v := by
  refine oh_ind_pk (p := fun x => x * y ∈ Oh E v) ?_ (by simp [zero_mem]) (fun x y h h' => by rw [add_mul]; exact add_mem h h')
    (fun x h => by rw [neg_mul]; exact neg_mem h) hx
  intro a h1 h2 o
  refine oh_ind_pk (p := fun y => a • inclR (F := F) (AF F) (o : E) * y ∈ Oh E v) ?_ (by simp [zero_mem])
    (fun x y h h' => by rw [mul_add]; exact add_mem h h') (fun x h => by rw [mul_neg]; exact neg_mem h) hy
  intro a' h1' h2' o'
  have e : a • inclR (F := F) (AF F) (o : E) * a' • inclR (F := F) (AF F) (o' : E) =
      (a * a') • inclR (F := F) (AF F) ((o * o' : 𝓞 E) : E) := by
    rw [smul_mul_smul_comm, ← map_mul]; rfl
  rw [e]
  exact oh_gen_pk (at_mulA_pk h1 a') (by rw [map_mul]; exact mul_mem h2 h2') _
private theorem oh_sg_pk {t : Fv F v} (ht : t ∈ v.adicCompletionIntegers F) : sg v t • (1 : AE F E) ∈ Oh E v := by
  have := oh_gen_pk (E := E) (PositivityTheory.ThKH.Iwas.at_sg t) (by rw [PositivityTheory.ThKH.Iwas.ev_sg]; exact ht) (1 : 𝓞 E)
  simpa using this
private theorem oh_smul_pk {t : Fv F v} (ht : t ∈ v.adicCompletionIntegers F) {x : AE F E} (hx : x ∈ Oh E v) :
    sg v t • x ∈ Oh E v := by
  have := oh_mul_pk (oh_sg_pk (E := E) ht) hx
  rwa [smul_mul_assoc, one_mul] at this
private theorem oh_matmul_pk {P Q : Matrix (Fin n) (Fin n) (AE F E)} (hP : ∀ i j, P i j ∈ Oh E v) (hQ : ∀ i j, Q i j ∈ Oh E v) (i j : Fin n) :
    (P * Q) i j ∈ Oh E v := by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => oh_mul_pk (hP i k) (hQ k j)
private theorem oh_mulVec_pk {P : Matrix (Fin n) (Fin n) (AE F E)} {w : Fin n → AE F E} (hP : ∀ i j, P i j ∈ Oh E v) (hw : ∀ i, w i ∈ Oh E v) (i : Fin n) :
    (P *ᵥ w) i ∈ Oh E v := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun k _ => oh_mul_pk (hP i k) (hw k)
private theorem lat_ind_pk {m : ℕ} {X : Spc F E m} {p : (Fin m → AE F E) → Prop}
    (gen : ∀ a : AF F, At (evFin F v) a → evFin F v a ∈ v.adicCompletionIntegers F → ∀ y ∈ X.L, p (fun i => a • inclR (F := F) (AF F) (y i)))
    (zero : p 0) (add : ∀ x y, p x → p y → p (x + y)) (neg : ∀ x, p x → p (-x)) {x : Fin m → AE F E} (hx : x ∈ PositivityTheory.ThK.latW X v) : p x := by
  refine AddSubgroup.closure_induction (p := fun x _ => p x) ?_ zero (fun x y _ _ h h' => add x y h h') (fun x _ h => neg x h) hx
  rintro _ ⟨a, h1, h2, y, hy, rfl⟩
  exact gen a h1 h2 y hy
private theorem lat_smul_pk {m : ℕ} {X : Spc F E m} {o : AE F E} (ho : o ∈ Oh E v) {z : Fin m → AE F E} (hz : z ∈ PositivityTheory.ThK.latW X v) :
    (fun i => o * z i) ∈ PositivityTheory.ThK.latW X v := by
  refine oh_ind_pk (p := fun o => (fun i => o * z i) ∈ PositivityTheory.ThK.latW X v) ?_ (by simp only [zero_mul]; exact zero_mem _)
    (fun x y h h' => by simp only [add_mul]; exact add_mem h h') (fun x h => by simp only [neg_mul]; exact neg_mem h) ho
  intro a h1 h2 o
  refine lat_ind_pk (p := fun z => (fun i => a • inclR (F := F) (AF F) (o : E) * z i) ∈ PositivityTheory.ThK.latW X v) ?_ (by simp only [Pi.zero_apply, mul_zero]; exact zero_mem _)
    (fun x y h h' => by simp only [Pi.add_apply, mul_add]; exact add_mem h h')
    (fun x h => by simp only [Pi.neg_apply, mul_neg]; exact neg_mem h) hz
  intro a' h1' h2' y hy
  refine AddSubgroup.subset_closure ⟨a * a', at_mulA_pk h1 a', by rw [map_mul]; exact mul_mem h2 h2', o • y, X.L.smul_mem o hy, ?_⟩
  funext i
  rw [smul_mul_smul_comm, ← map_mul]
  rfl
private theorem lat_mulVec_pk {m : ℕ} {X : Spc F E m} {P : Matrix (Fin m) (Fin n) (AE F E)} {w : Fin n → AE F E}
    (hP : ∀ j, (fun i => P i j) ∈ PositivityTheory.ThK.latW X v) (hw : ∀ j, w j ∈ Oh E v) : P *ᵥ w ∈ PositivityTheory.ThK.latW X v := by
  have e : P *ᵥ w = ∑ j, fun i => w j * P i j := by
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [e]
  exact sum_mem fun j _ => lat_smul_pk (hw j) (hP j)
private theorem vmv_mem_pk {X : Spc F E n} {W : Spc F E d} {z : Fin n → AE F E} {y : Fin d → AE F E}
    (hz : z ∈ PositivityTheory.ThK.latW X v) (hy : y ∈ PositivityTheory.ThK.latW W v) : Matrix.vecMulVec z y ∈ latAtV X W v := by
  refine lat_ind_pk (p := fun z => Matrix.vecMulVec z y ∈ latAtV X W v) ?_ ?_ ?_ ?_ hz
  · intro a h1 h2 x hx
    refine lat_ind_pk (p := fun y => Matrix.vecMulVec (fun i => a • inclR (F := F) (AF F) (x i)) y ∈ latAtV X W v) ?_ ?_ ?_ ?_ hy
    · intro a' h1' h2' y hy
      refine AddSubgroup.subset_closure ⟨a * a', at_mulA_pk h1 a', by rw [map_mul]; exact mul_mem h2 h2', x, hx, y, hy, ?_⟩
      ext i j
      simp [Matrix.vecMulVec_apply, incM, smul_mul_smul_comm]
      rw [mul_comm a a', mul_smul]
    · have e : Matrix.vecMulVec (fun i => a • inclR (F := F) (AF F) (x i)) (0 : Fin d → AE F E) = 0 := by
        ext i j; simp [Matrix.vecMulVec_apply]
      rw [e]; exact zero_mem _
    · intro x y h h'
      have := add_mem h h'
      rwa [show ∀ u (p q : Fin d → AE F E), Matrix.vecMulVec u p + Matrix.vecMulVec u q = Matrix.vecMulVec u (p + q) from fun u p q => by
        ext i j; simp [Matrix.vecMulVec_apply, mul_add]] at this
    · intro x h
      have := neg_mem h
      rwa [show ∀ u (p : Fin d → AE F E), -Matrix.vecMulVec u p = Matrix.vecMulVec u (-p) from fun u p => by
        ext i j; simp [Matrix.vecMulVec_apply]] at this
  · have e : Matrix.vecMulVec (0 : Fin n → AE F E) y = 0 := by
      ext i j; simp [Matrix.vecMulVec_apply]
    rw [e]; exact zero_mem _
  · intro x y h h'
    have := add_mem h h'
    rwa [show ∀ (p q : Fin n → AE F E) u, Matrix.vecMulVec p u + Matrix.vecMulVec q u = Matrix.vecMulVec (p + q) u from fun p q u => by
      ext i j; simp [Matrix.vecMulVec_apply, add_mul]] at this
  · intro x h
    have := neg_mem h
    rwa [show ∀ (p : Fin n → AE F E) u, -Matrix.vecMulVec p u = Matrix.vecMulVec (-p) u from fun p u => by
      ext i j; simp [Matrix.vecMulVec_apply]] at this
private theorem gam_ind_pk {X : Spc F E n} {W : Spc F E d} {p : Matrix (Fin n) (Fin d) (AE F E) → Prop}
    (gen : ∀ z ∈ PositivityTheory.ThK.latW X v, ∀ y ∈ PositivityTheory.ThK.latW W v, p (Matrix.vecMulVec z y))
    (zero : p 0) (add : ∀ x y, p x → p y → p (x + y)) (neg : ∀ x, p x → p (-x)) {γ : Matrix (Fin n) (Fin d) (AE F E)}
    (hγ : γ ∈ latAtV X W v) : p γ := by
  refine AddSubgroup.closure_induction (p := fun x _ => p x) ?_ zero (fun x y _ _ h h' => add x y h h') (fun x _ h => neg x h) hγ
  rintro _ ⟨a, h1, h2, x, hx, y, hy, rfl⟩
  have e : a • incM F (Matrix.vecMulVec x y) = Matrix.vecMulVec (fun i => a • inclR (F := F) (AF F) (x i))
      (fun j => sg v 1 • inclR (F := F) (AF F) (y j)) := by
    ext i j
    have e1 : a * sg v 1 = a := by rw [mul_comm]; exact at_self_pk h1
    simp [Matrix.vecMulVec_apply, incM, smul_mul_smul_comm, e1]
    rw [← mul_smul, mul_comm (sg v 1) a, e1]
  rw [e]
  exact gen _ (AddSubgroup.subset_closure ⟨a, h1, h2, x, hx, rfl⟩) _
    (AddSubgroup.subset_closure ⟨sg v 1, PositivityTheory.ThKH.Iwas.at_sg 1, sg_one_int_pk, y, hy, rfl⟩)
private theorem mul_eM_pk {M : Matrix (Fin n) (Fin n) (AE F E)} (h : At (evFin F v) M) : M * eM v n = M := by
  rw [Matrix.mul_smul, Matrix.mul_one]; exact at_self_pk h
private theorem eM_mul_pk {M : Matrix (Fin n) (Fin n) (AE F E)} (h : At (evFin F v) M) : eM v n * M = M := by
  rw [Matrix.smul_mul, Matrix.one_mul]; exact at_self_pk h
private theorem eM_mem_pk (i j : Fin n) : (eM (E := E) v n) i j ∈ Oh E v := by
  by_cases h : i = j
  · subst h
    simpa [eM] using oh_sg_pk (E := E) (v := v) (one_mem _)
  · simp [eM, h, zero_mem]
private theorem eM_at_pk : At (evFin F v) (eM (E := E) v n) := fun u hu => by
  rw [smul_smul, show u * sg v 1 = 0 from PositivityTheory.ThKH.Iwas.at_sg 1 u hu, zero_smul]
end UpperTheory.LatD
theorem UpperTheory.exists_weilLatticeDatum :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → X.IsHerm σ B r s → W.IsSkew σ B r' s' → 2 * n ≤ d → ∀ v : Pl F, ∃ Λ x₁ R ϖ, LatData σ X W v Λ x₁ R ϖ := by
  intro F E _ _ _ _ _ σ B n d X W r s r' s' hB hX hW hnd v
  have hYR : ∃ Y R, IsIsoW σ W v (n := n) Y R := by
    by_cases ht : Nonempty (E →ₐ[F] Fv F v)
    · obtain ⟨t⟩ := ht
      exact _root_.UpperTheory.exists_isotropic_splitting_of_two_mul_le F E σ B n d W r' s' hB hW hnd v t
    · obtain ⟨w, hw⟩ := _root_.PositivityTheory.ThK.inertof_proof_k F E σ B hB v (not_nonempty_iff.1 ht)
      exact _root_.UpperTheory.exists_isotropic_splitting_at_inert_prime F E σ B n d W r' s' hB hW hnd v w hw
  obtain ⟨Y, R, hY⟩ := hYR
  obtain ⟨b, c, hF⟩ := UpperTheory.unitaryLattice_exists_frame F E n X v hX.lat
  obtain ⟨ϖ, hϖ0, hϖ1⟩ : ∃ ϖ : Fv F v, ϖ ≠ 0 ∧ Valued.v ϖ < 1 := by
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
    have e : Valued.v ((π : F) : v.adicCompletion F) = v.valuation F π := v.valuedAdicCompletion_eq_valuation' π
    refine ⟨((π : F) : v.adicCompletion F), ?_, ?_⟩
    · intro h0
      rw [h0, map_zero, hπ] at e
      exact absurd e.symm (by simp)
    · rw [e, hπ]
      exact compareOfLessAndEq_eq_lt.mp rfl
  have hϖm : ϖ ∈ v.adicCompletionIntegers F := hϖ1.le
  have hmul : ∀ a ∈ abelian₂ (E := E) v b c, ∀ a' ∈ abelian₂ (E := E) v b c, a * a' ∈ abelian₂ (E := E) v b c := by
    intro a ha a' ha'
    refine ⟨PositivityTheory.ThKH.Iwas.at_mul_left ha.1 a', fun i j => ?_⟩
    have e : c * (a * a') * b = (c * a * b) * (c * a' * b) := by
      calc c * (a * a') * b = c * (a * eM v n * a') * b := by rw [UpperTheory.LatD.mul_eM_pk ha.1]
        _ = c * (a * (b * c) * a') * b := by rw [hF.bc]
        _ = (c * a * b) * (c * a' * b) := by simp only [Matrix.mul_assoc]
    rw [e]
    exact UpperTheory.LatD.oh_matmul_pk ha.2 ha'.2 i j
  have hact : ∀ a ∈ abelian₂ (E := E) v b c, ∀ z ∈ PositivityTheory.ThK.latW X v, a *ᵥ z ∈ PositivityTheory.ThK.latW X v := by
    intro a ha z hz
    have e : a *ᵥ z = b *ᵥ ((c * a * b) *ᵥ (c *ᵥ z)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      congr 1
      calc a = eM v n * a * eM v n := by rw [UpperTheory.LatD.mul_eM_pk (PositivityTheory.ThKH.Iwas.at_mul_right _ ha.1), UpperTheory.LatD.eM_mul_pk ha.1]
        _ = (b * c) * a * (b * c) := by rw [hF.bc]
        _ = b * (c * a * b) * c := by simp only [Matrix.mul_assoc]
    rw [e]
    exact UpperTheory.LatD.lat_mulVec_pk hF.col (UpperTheory.LatD.oh_mulVec_pk ha.2 (hF.coord z hz))
  refine ⟨abelian₂ (E := E) v b c, b * Y, R * c, ϖ, ?_⟩
  refine
    { at_mem := fun a ha => ha.1
      one_mem := ⟨UpperTheory.LatD.eM_at_pk, fun i j => ?_⟩
      mul_mem := hmul
      smul_mem := fun t ht a ha => ⟨fun u hu => by rw [smul_comm, ha.1 u hu, smul_zero], fun i j => ?_⟩
      act := ?_
      x_mem := ?_
      gram := ?_
      right := ?_
      r_mem := ?_
      ϖ_ne := hϖ0
      ϖ_mem := hϖm
      unit := UpperTheory.latticeOrder_exists_inverse_one_add_uniformizer_smul F E n X v b c hF ϖ hϖm hϖ1
      small := (UpperTheory.mem_nhds_one_of_congruence_latticeOrder F E σ n X v b c hF ϖ hϖ0 hϖ1).1
      nbhd := (UpperTheory.mem_nhds_one_of_congruence_latticeOrder F E σ n X v b c hF ϖ hϖ0 hϖ1).2 }
  · rw [UpperTheory.LatD.mul_eM_pk hF.at_c, hF.cb]
    exact UpperTheory.LatD.eM_mem_pk i j
  · rw [Matrix.mul_smul, Matrix.smul_mul]
    exact UpperTheory.LatD.oh_smul_pk ht (ha.2 i j)
  · intro a ha γ hγ
    refine UpperTheory.LatD.gam_ind_pk (p := fun γ => a * γ ∈ latAtV X W v) ?_ (by simp [zero_mem]) ?_ ?_ hγ
    · intro z hz y hy
      rw [Matrix.mul_vecMulVec]
      exact UpperTheory.LatD.vmv_mem_pk (hact a ha z hz) hy
    · intro x y h h'
      rw [Matrix.mul_add]; exact add_mem h h'
    · intro x h
      rw [Matrix.mul_neg]; exact neg_mem h
  · have e : b * Y = ∑ k, Matrix.vecMulVec (fun i => b i k) (Y k) := by
      ext i j
      simp [Matrix.mul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply]
    rw [e]
    exact sum_mem fun k _ => UpperTheory.LatD.vmv_mem_pk (hF.col k) (hY.what₂ k)
  · have hm : (b * Y).map (cA σ) = b.map (cA σ) * Y.map (cA σ) := Matrix.map_mul (f := (cA σ).toRingHom)
    rw [hm, Matrix.transpose_mul]
    have e : b * Y * incM F W.J * ((Y.map (cA σ))ᵀ * (b.map (cA σ))ᵀ) =
        b * (Y * incM F W.J * (Y.map (cA σ))ᵀ) * (b.map (cA σ))ᵀ := by simp only [Matrix.mul_assoc]
    rw [e, hY.gram, Matrix.mul_zero, Matrix.zero_mul]
  · have e : b * Y * (R * c) = b * (Y * R) * c := by simp only [Matrix.mul_assoc]
    rw [e, hY.right, UpperTheory.LatD.mul_eM_pk hF.at_b, hF.bc]
  · intro γ hγ
    refine ⟨PositivityTheory.ThKH.Iwas.at_mul_right _ (PositivityTheory.ThKH.Iwas.at_mul_right _ hF.at_c), ?_⟩
    refine UpperTheory.LatD.gam_ind_pk (p := fun γ => ∀ i j, (c * (γ * (R * c)) * b) i j ∈ Oh E v) ?_ (by simp [zero_mem]) ?_ ?_ hγ
    · intro z hz y hy i j
      have e : c * (Matrix.vecMulVec z y * (R * c)) * b = Matrix.vecMulVec (c *ᵥ z) (sg v 1 • (y ᵥ* R)) := by
        have e1 : c * (Matrix.vecMulVec z y * (R * c)) * b = c * Matrix.vecMulVec z y * R * (c * b) := by
          simp only [Matrix.mul_assoc]
        rw [e1, hF.cb, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.mul_smul, Matrix.mul_one]
        ext i j
        simp [Matrix.vecMulVec_apply]
      rw [e, Matrix.vecMulVec_apply]
      exact UpperTheory.LatD.oh_mul_pk (hF.coord z hz i) (UpperTheory.LatD.oh_smul_pk (one_mem _) (hY.coord y hy j))
    · intro x y h h' i j
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.add_mul]
      exact add_mem (h i j) (h' i j)
    · intro x h i j
      rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.neg_mul]
      exact neg_mem (h i j)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.HeightFunctionContinuousPos
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_function_continuous_pos : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → Continuous a ∧ ∀ x, 0 < a x := by
  first | exact @_root_.GlobalTheory.CompanionTheory.Iwasawa.height_continuous_pos_k | exact _root_.GlobalTheory.CompanionTheory.Iwasawa.height_continuous_pos_k | (intros; apply _root_.GlobalTheory.CompanionTheory.Iwasawa.height_continuous_pos_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.JHomValK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def jHom_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) :
    G2 σ Y →* GL (Fin d.n ⊕ Fin d.n) (AE F E) :=
  (MulAut.conj (bA d.b)).toMonoidHom.comp ((blkGL h).comp
    ((MulAut.conj (bA (F := F) b)⁻¹).toMonoidHom.comp (UG (cA σ) (dbl (incM F Y.J))).subtype))
theorem jHom_val_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) (g : G2 σ Y) :
    (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g).1 = incM F d.b.1 * blk h (inFrame b g) 1 * incM F (d.b⁻¹).1 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_subtype,
    Units.val_mul, bA_val, bA_inv_val, blkGL, Units.coe_map, blkHom, MonoidHom.coe_mk, OneHom.coe_mk, inFrame_eq]
theorem jHom_mem_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ)
    (e1 : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε) (e2 : b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε) (g : G2 σ Y) :
    _root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
  have hG1 : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom = incM F (jeps d.n ε) := by
    rw [← e1, ← incM_gram, incM_dbl]; rfl
  have hG2 : (incM F b.1)ᵀ * dbl (incM F Y.J) * (incM F b.1).map (cA σ).toRingHom = incM F (jeps n ε) := by
    rw [← e2, ← incM_gram, incM_dbl]; rfl
  have hg : (g.1.1)ᵀ * dbl (incM F Y.J) * (g.1.1).map (cA σ).toRingHom = dbl (incM F Y.J) := g.2
  have hM := (unitary_conj_iff (cA σ).toRingHom _ _ _ _ g.1.1 (incM_mul_inv b) (incM_inv_mul b) hG2).1 hg
  rw [← inFrame_eq] at hM
  show (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g).1ᵀ * dbl (incM F d.Y.J) * (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g).1.map (cA σ).toRingHom = dbl (incM F d.Y.J)
  rw [unitary_conj_iff (cA σ).toRingHom _ _ _ _ _ (incM_mul_inv d.b) (incM_inv_mul d.b) hG1, _root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_val_k]
  have eQP : incM F (d.b⁻¹).1 * (incM F d.b.1 * blk h (inFrame b g) 1 * incM F (d.b⁻¹).1) * incM F d.b.1 =
      blk h (inFrame b g) 1 := by
    simp only [← Matrix.mul_assoc, incM_inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, incM_inv_mul, Matrix.mul_one]
  rw [eQP, incM_jeps, jepsR_blk h, ← incM_jeps, ← incM_jeps, blk_transpose, blk_map _ _ _ _ (map_zero _), blk_mul,
    blk_mul, hM]
  congr 1
  simp [Matrix.map_one _ (map_zero _) (map_one _)]
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LevelK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThKEst
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem level_k : _root_.PositivityTheory.ThKEst.Level_k := _root_.PositivityTheory.ThKEst.level_of_k _root_.PositivityTheory.ThKEst.coefEq_of_k fourierInj_of (_root_.PositivityTheory.ThKEst.coefBd_of_k coefReal_of)
end PositivityTheory.ThKEst
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LintegralEnormSqLatRepApplyEq
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_enorm_sq_latRep_apply_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
          IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ p f,
            ∫⁻ w in 𝓕, ‖(Om p f : WOF F E nS nT → ℂ) w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖(f : WOF F E nS nT → ℂ) w‖ₑ ^ 2 ∂μ := by
  first | exact @_root_.GlobalTheory.FinLatUnitF.lintegral_sq_Om_k | exact _root_.GlobalTheory.FinLatUnitF.lintegral_sq_Om_k | (intros; apply _root_.GlobalTheory.FinLatUnitF.lintegral_sq_Om_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SchrodingerModelIntertwining
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_model_intertwining : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (N : ℕ) (e : Formalism.IndefR.DatumF.WOF F E nS nT ≃ₗ[AF F] GlobalTheory.ThetaTransform.VA F N),
        (∀ w w', Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ w w' = GlobalTheory.ThetaTransform.symV (e w) (e w')) →
        (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin N → F,
          e (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) →
        ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f →
          ∃ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), GlobalTheory.ThetaTransform.thV B.ψ Φ ∘ e = f := by
  first | exact @_root_.GlobalTheory.ThetaOntoF.exists_thV_eqF_k | exact _root_.GlobalTheory.ThetaOntoF.exists_thV_eqF_k | (intros; apply _root_.GlobalTheory.ThetaOntoF.exists_thV_eqF_k <;> assumption)
end
end

