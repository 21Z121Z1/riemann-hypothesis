import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1401
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1952
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1946
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1941
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0145
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0034

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceWeilNormalisesHeisenberg
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertBridge

theorem weil_normalises_heis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (AE F E))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)),
      (∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M'.co.rho B.ψ (κ x))
        (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ)) →
    ∀ ω : (Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) × Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →*
        Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v))),
      (∀ g h (m : SB (Fin a' × Fin (a + a') → Fv F v)) (φ₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
        φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v) →
        (Acts (evFin F v) (om' (ιS g, ιT h)) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          ((ω (g, h) m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = φ₁)) →
    ∀ g h x, ω (g, h) * ρ x =
      ρ (((h : GL (Fin (a + a')) L) : Matrix (Fin (a + a')) (Fin (a + a')) L) * x *
        (((g : GL (Fin a') L)⁻¹ : GL (Fin a') L) : Matrix (Fin a') (Fin a') L)) * ω (g, h) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w _ _ L _ _ ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ ω hω g h x
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hEq, _, _, _, _⟩ := hC
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (F := F) (Fin a' × Fin (a + a')) v
  have hS := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'
  have hωA : ∀ (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (om' (ιS g, ιT h))
      (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ω (g, h) m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) :=
    fun m => (hω g h m _ (ω (g, h) m).2).2 rfl
  refine LinearMap.ext fun m => ?_
  apply Subtype.ext
  set y := ((h : GL (Fin (a + a')) L) : Matrix (Fin (a + a')) (Fin (a + a')) L) * x *
        (((g : GL (Fin a') L)⁻¹ : GL (Fin a') L) : Matrix (Fin a') (Fin a') L) with hy
  have e1 : om' (ιS g, ιT h) (G.M'.co.rho B.ψ (κ x) (tens (evFin F v) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) R)) =
      tens (evFin F v) (((ω (g, h) (ρ x m)) : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) R := by
    rw [hρ x m R (hR _ m.2), hωA (ρ x m) R (hR _ (ρ x m).2)]
  have e2 : om' (ιS g, ιT h) (G.M'.co.rho B.ψ (κ x) (tens (evFin F v) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) R)) =
      tens (evFin F v) (((ρ y (ω (g, h) m)) : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) R := by
    rw [hS.impl (ιS g, ιT h) (κ x) _ (hR _ m.2).2, hEq g h x, ← hy, hωA m R (hR _ m.2),
      hρ y (ω (g, h) m) R (hR _ (ω (g, h) m).2)]
  have e := e1.symm.trans e2
  show (((ω (g, h) (ρ x m)) : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) =
    (((ρ y (ω (g, h) m)) : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ)
  funext yv
  set z : (Fin a' × Fin (a + a')) → AF F := fun i => GlobalTheory.LatVac.liftV v (yv i) with hz
  have hza : At (evFin F v) z := GlobalTheory.VacAny.at_pi fun i => GlobalTheory.LatVac.at_liftV v _
  have hrx : R (0 + z) = R 0 := (hR _ m.2).1 0 z hza
  have hyv : (fun i => evFin F v (((0 : (Fin a' × Fin (a + a')) → AF F) + z) i)) = yv := by
    funext i
    simp only [hz, Pi.add_apply, Pi.zero_apply, zero_add, GlobalTheory.LatVac.evFin_liftV]
  have e' := congrFun e (0 + z)
  simp only [tens] at e'
  rw [hrx, hyv] at e'
  exact mul_right_cancel₀ hR0 e'

end GlobalTheory.InertBridge

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPointMemTensorLatticeIffIntegralCoords
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.InertCoord
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertLat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)

theorem ptAt_complMap (b : Fv F v) : ptAt hw h (complMap h b) = GlobalTheory.LatVac.liftV v b • (1 : AE F E) := by
  have hat : At (evFin F v) (GlobalTheory.LatVac.liftV v b • (1 : AE F E)) := by
    intro u hu
    rw [smul_smul, ← smul_eq_mul, GlobalTheory.LatVac.at_liftV v b u hu, zero_smul]
  rw [← ptAt_locW hw h hat]
  congr 1
  change complMap h b = toCompl h (compFin F E v (GlobalTheory.LatVac.liftV v b • (1 : AE F E)))
  rw [GlobalTheory.ThK.compFin_smul, map_one, GlobalTheory.LatVac.evFin_liftV, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul',
    toCompl_tmul, smul_eq_mul, mul_one, map_one, mul_one]

theorem locW_smul_inclR (a : AF F) (e : E) :
    locW h (a • inclR (F := F) (AF F) e) = complMap h (evFin F v a) * algebraMap E _ e := by
  change toCompl h (compFin F E v (a • ((1 : AF F) ⊗ₜ[F] e))) = _
  rw [GlobalTheory.ThK.compFin_smul, GlobalTheory.AdelicU.Supp.compFin_one_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one, toCompl_tmul]

theorem mul_vecMulVec_mul {R : Type} [CommRing R] {m k : ℕ} (M : Matrix (Fin m) (Fin m) R) (N : Matrix (Fin k) (Fin k) R)
    (p : Fin m → R) (q : Fin k → R) : M * Matrix.vecMulVec p q * Nᵀ = Matrix.vecMulVec (M *ᵥ p) (N *ᵥ q) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem mul_transpose_mul_eq_sum {R : Type} [CommRing R] {m k : ℕ} (A : Matrix (Fin m) (Fin m) R)
    (B : Matrix (Fin k) (Fin k) R) (x : Matrix (Fin k) (Fin m) R) :
    A * xᵀ * Bᵀ = ∑ i, ∑ j, x j i • Matrix.vecMulVec (Aᵀ i) (Bᵀ j) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.InertLat

namespace GlobalTheory.InertLat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
  {n d : ℕ} (X : Spc F E n) (Y : Spc F E d)

theorem smul_mem_latAtV {t : w.adicCompletion E} (ht : t ∈ Formalism.UG.Ov E w) {γ : Matrix (Fin n) (Fin d) (AE F E)}
    (hγ : γ ∈ latAtV X Y v) : ptAt hw h t • γ ∈ latAtV X Y v := by
  obtain ⟨y, rfl⟩ := InertChart.toCompl_surjective h t
  have hy := (InertChart.mem_intLoc_iff hw h y).2 ht
  refine intLoc_induction (p := fun y => ∀ γ ∈ latAtV X Y v, ptAt hw h (toCompl h y) • γ ∈ latAtV X Y v)
    ?_ ?_ ?_ ?_ hy γ hγ
  · intro a ha o γ hγ
    rw [toCompl_tmul, mul_comm, ← inclR_mul_ptAt, ptAt_complMap]
    induction hγ using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a', ha', hv, x, hx, y, hy, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v a * a', ?_, ?_, (o • x), X.L.smul_mem o hx, y, hy, ?_⟩
      · intro u hu
        rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a', ha' u hu, mul_zero]
      · rw [map_mul, GlobalTheory.LatVac.evFin_liftV]
        exact mul_mem ha hv
      · ext k l
        simp only [incM, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
          Algebra.smul_def, map_mul]
        rw [show algebraMap (𝓞 E) E o = (o : E) from rfl]
        ring
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  · intro γ hγ; rw [map_zero, map_zero, zero_smul]; exact zero_mem _
  · intro y z hy hz γ hγ; rw [map_add, map_add, add_smul]; exact add_mem (hy γ hγ) (hz γ hγ)
  · intro y hy γ hγ; rw [map_neg, map_neg, neg_smul]; exact neg_mem (hy γ hγ)

end GlobalTheory.InertLat

namespace GlobalTheory.InertLat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
  {n d : ℕ} (X : Spc F E n) (Y : Spc F E d)

theorem ptAt_algebraMap (e : E) :
    ptAt hw h (algebraMap E (w.adicCompletion E) e) = GlobalTheory.LatVac.liftV v 1 • inclR (F := F) (AF F) e := by
  have := inclR_mul_ptAt hw h e 1
  rw [mul_one, ← (complMap h).map_one, ptAt_complMap, mul_smul_comm, mul_one] at this
  exact this.symm

theorem vecMulVec_mem {p : Fin n → w.adicCompletion E} (hp : p ∈ latAt w X.L) {q : Fin d → w.adicCompletion E}
    (hq : q ∈ latAt w Y.L) : (Matrix.vecMulVec p q).map (ptAt hw h) ∈ latAtV X Y v := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨x, hx, rfl⟩ := hp
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨y, hy, rfl⟩ := hq
      refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v 1, GlobalTheory.LatVac.at_liftV v 1, ?_, x, hx, y, hy, ?_⟩
      · rw [GlobalTheory.LatVac.evFin_liftV]; exact one_mem _
      · ext k l
        simp only [incM, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, ← map_mul, ptAt_algebraMap]
    | zero =>
      convert zero_mem (latAtV X Y v) using 1
      ext k l; simp [Matrix.vecMulVec_apply]
    | add q q' _ _ h1 h2 =>
      convert add_mem h1 h2 using 1
      ext k l; simp [Matrix.vecMulVec_apply, mul_add]
    | smul t q _ h1 =>
      convert smul_mem_latAtV hw h X Y t.2 h1 using 1
      ext k l
      simp only [Matrix.map_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, ← map_mul]
      congr 1
      rw [Subring.smul_def, smul_eq_mul]
      ring
  | zero =>
    convert zero_mem (latAtV X Y v) using 1
    ext k l; simp [Matrix.vecMulVec_apply]
  | add p p' _ _ h1 h2 =>
    convert add_mem h1 h2 using 1
    ext k l; simp [Matrix.vecMulVec_apply, add_mul]
  | smul t p _ h1 =>
    convert smul_mem_latAtV hw h X Y t.2 h1 using 1
    ext k l
    simp only [Matrix.map_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, ← map_mul]
    congr 1
    rw [Subring.smul_def, smul_eq_mul]
    ring

end GlobalTheory.InertLat

namespace GlobalTheory.InertLat

open GlobalTheory.InertCoord in

theorem kap_mem_latAtV_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F)
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (A : GL (Fin n) (w.adicCompletion E)) (Bm : GL (Fin d) (w.adicCompletion E)),
    IsFrameAt w X.L A → IsFrameAt w Y.L Bm → ∀ x,
      (∀ i j, x i j ∈ Formalism.UG.intL (w.adicCompletion E)) ↔
        kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x ∈ latAtV X Y v := by
  intro F E _ _ _ _ _ v w hw h n d X Y A Bm hA hB x
  have col : ∀ {m : ℕ} {L : Submodule (𝓞 E) (Fin m → E)} {C : GL (Fin m) (w.adicCompletion E)},
      IsFrameAt w L C → ∀ i, (C : Matrix (Fin m) (Fin m) (w.adicCompletion E))ᵀ i ∈ latAt w L := by
    intro m L C hC i
    have := (hC (Pi.single i 1)).1 fun k => by
      by_cases e : k = i
      · subst e; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne e]; exact zero_mem _
    rwa [Matrix.mulVec_single_one] at this
  have inv : ∀ {m : ℕ} {L : Submodule (𝓞 E) (Fin m → E)} {C : GL (Fin m) (w.adicCompletion E)},
      IsFrameAt w L C → ∀ z ∈ L, ∀ k, ((↑C⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ
        fun i => algebraMap E (w.adicCompletion E) (z i)) k ∈ Formalism.UG.Ov E w := by
    intro m L C hC z hz
    refine (hC _).2 ?_
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    exact Submodule.subset_span ⟨z, hz, rfl⟩
  constructor
  · intro hx
    rw [kap_apply, mul_transpose_mul_eq_sum]
    change _ ∈ (latAtV X Y v).comap (AddMonoidHom.mapMatrix (ptAt hw h).toAddMonoidHom)
    refine sum_mem fun i _ => sum_mem fun j _ => ?_
    change (x j i • Matrix.vecMulVec _ _).map (ptAt hw h) ∈ latAtV X Y v
    convert smul_mem_latAtV hw h X Y (hx j i) (vecMulVec_mem hw h X Y (col hA i) (col hB j)) using 1
    ext k l
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  · intro hk i j
    let Ψ : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n) (Fin d) (w.adicCompletion E) := fun γ =>
      (↑A⁻¹ : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * AddMonoidHom.mapMatrix (locW h).toAddMonoidHom γ *
        (↑Bm⁻¹ : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ
    have hΨ : ∀ γ ∈ latAtV X Y v, ∀ k l, Ψ γ k l ∈ Formalism.UG.Ov E w := by
      intro γ hγ
      induction hγ using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, -, ha, p, hp, q, hq, rfl⟩ := hz
        have e1 : AddMonoidHom.mapMatrix (locW h).toAddMonoidHom (a • incM F (Matrix.vecMulVec p q)) =
            complMap h (evFin F v a) • Matrix.vecMulVec (fun i => algebraMap E (w.adicCompletion E) (p i))
              (fun i => algebraMap E (w.adicCompletion E) (q i)) := by
          refine Matrix.ext fun k l => ?_
          change locW h (a • inclR (F := F) (AF F) (p k * q l)) = _
          rw [locW_smul_inclR, map_mul]
          simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
        intro k l
        simp only [Ψ, e1, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec_mul, Matrix.smul_apply,
          Matrix.vecMulVec_apply, smul_eq_mul]
        exact mul_mem (complMap_mem h ha) (mul_mem (inv hA p hp k) (inv hB q hq l))
      | zero => intro k l; simp [Ψ]
      | add x y _ _ hx hy =>
        intro k l
        simp only [Ψ, map_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
        exact add_mem (hx k l) (hy k l)
      | neg x _ hx =>
        intro k l
        simp only [Ψ, map_neg, Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply]
        exact neg_mem (hx k l)
    have e : Ψ (kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E))
        (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x) = xᵀ := by
      have e2 : AddMonoidHom.mapMatrix (locW h).toAddMonoidHom (kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E))
          (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x) =
          (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * xᵀ * (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ := by
        refine Matrix.ext fun k l => ?_
        simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, kap_apply, RingHom.toAddMonoidHom_eq_coe,
          AddMonoidHom.coe_coe, locW_ptAt]
      simp only [Ψ, e2]
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mul]
    have := hΨ _ hk j i
    rw [e] at this
    exact this

end GlobalTheory.InertLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrablePowerNormCompact
section
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
open scoped TensorProduct NNReal ENNReal

noncomputable section
namespace GlobalTheory.LocTateInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F)

theorem finite_FE : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E

attribute [local instance] finite_FE

def basisEv : Module.Basis (Fin (Module.finrank F E)) (Fv F v) (Fv F v ⊗[F] E) :=
  Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)

theorem isModuleTopology_Ev : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩

def coordEv : (Fv F v ⊗[F] E) ≃ₜ+ (Fin (Module.finrank F E) → Fv F v) :=
  haveI := isModuleTopology_Ev (E := E) v
  { (basisEv v).equivFun.toAddEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap (basisEv (E := E) v).equivFun.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap (basisEv (E := E) v).equivFun.symm.toLinearMap }

theorem isTopologicalRing_Ev : IsTopologicalRing (Fv F v ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens

theorem t2Space_Fv_tensor : T2Space (Fv F v ⊗[F] E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension

theorem locallyCompactSpace_Ev : LocallyCompactSpace (Fv F v ⊗[F] E) :=
  haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v
  (coordEv (E := E) v).toHomeomorph.isClosedEmbedding.locallyCompactSpace

theorem secondCountable_Ev : SecondCountableTopology (Fv F v ⊗[F] E) :=
  haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v
  (coordEv (E := E) v).toHomeomorph.isEmbedding.secondCountableTopology

theorem isOpenUnits_Ev : IsOpenUnits (Fv F v ⊗[F] E) :=
  haveI := isModuleTopology_Ev (E := E) v
  haveI := isTopologicalRing_Ev (E := E) v
  GlobalTheory.GaugeEx.isOpenUnits_of_basis (basisEv v)

attribute [local instance] isTopologicalRing_Ev t2Space_Fv_tensor locallyCompactSpace_Ev secondCountable_Ev isOpenUnits_Ev

theorem distribHaarChar_Ev (u : (Fv F v ⊗[F] E)ˣ) :
    distribHaarChar (Fv F v ⊗[F] E) u = ‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ := by
  borelize (Fv F v ⊗[F] E)
  haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  set b := basisEv (E := E) v
  set M := Algebra.leftMulMatrix b (u : Fv F v ⊗[F] E) with hMdef
  have hdet : M.det = Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E) := (Algebra.norm_eq_matrix_det b _).symm
  have hM : IsUnit M.det := hdet ▸ u.isUnit.map (Algebra.norm (Fv F v))
  have hN0 : Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E) ≠ 0 := (hdet ▸ hM).ne_zero
  rw [GlobalTheory.ModuNorm.distribHaarChar_eq_addEquivAddHaarChar]
  have ht := GlobalTheory.ModuLR.addEquivAddHaarChar_transport (coordEv (E := E) v).symm (GlobalTheory.ModuLR.mulVecCE M hM)
  have hext : (((coordEv (E := E) v).symm.symm.trans (GlobalTheory.ModuLR.mulVecCE M hM)).trans (coordEv (E := E) v).symm) =
      GlobalTheory.ModuNorm.mulUnitCE u := by
    ext x
    show b.equivFun.symm (Matrix.mulVec M (b.equivFun x)) = (u : Fv F v ⊗[F] E) * x
    rw [show Matrix.mulVec M (b.equivFun x) = b.equivFun ((u : Fv F v ⊗[F] E) * x) from Algebra.leftMulMatrix_mulVec_repr b _ x,
      LinearEquiv.symm_apply_apply]
  rw [hext] at ht
  rw [ht, GlobalTheory.ModuArtin.addEquivAddHaarChar_mulVecCE _ inferInstance inferInstance, hdet, GlobalTheory.GaugeEx.modu,
    dif_pos (hdet ▸ hM)]
  convert GlobalTheory.CompanionTheory.SW.ProdFormula.distribHaarChar_eq_nnnorm v _ hN0 using 2
  exact Units.ext rfl

end GlobalTheory.LocTateInt

namespace GlobalTheory.LocTateInt

open scoped Pointwise

attribute [local instance] finite_FE isTopologicalRing_Ev t2Space_Fv_tensor locallyCompactSpace_Ev secondCountable_Ev isOpenUnits_Ev

theorem integrable_indicator_absE_pow : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F)
    (μ : Measure (idelesAt E (evFin F v))), IsNormE E v μ → ∀ (C : Set (Fv F v ⊗[F] E)), IsCompact C → ∀ z : ℕ, 1 ≤ z →
      Integrable (fun l : idelesAt E (evFin F v) =>
        C.indicator (fun _ => ((GlobalTheory.Doubling.absE F E l.1 : ℝ)) ^ z) (compFin F E v l.1)) μ := by
  intro F E _ _ _ _ _ v μ hμ C hC z hz
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evFin F v)
  haveI := hμ.1
  borelize (Fv F v ⊗[F] E)
  set φ := idelesAtEquiv E v with hφ
  let j : idelesAt E (evFin F v) → Fv F v ⊗[F] E := fun l => ((φ l : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E)
  have hoe : Topology.IsOpenEmbedding j :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := Fv F v ⊗[F] E)).comp φ.toHomeomorph.isOpenEmbedding
  have hme : MeasurableEmbedding j := hoe.measurableEmbedding
  set lam : Measure (Fv F v ⊗[F] E) := Measure.addHaar with hlam
  set ν : Measure (idelesAt E (evFin F v)) := lam.comap j with hν
  have hνa : ∀ s, ν s = lam (j '' s) := fun s => hme.comap_apply lam s
  have hne : ∀ x : (Fv F v ⊗[F] E)ˣ, GlobalTheory.Doubling.absEv F E v x ≠ 0 := fun x h => by
    have e := congrArg (GlobalTheory.Doubling.absEv F E v) (mul_inv_cancel x)
    rw [map_mul, map_one, h, zero_mul] at e
    exact zero_ne_one e
  set f : idelesAt E (evFin F v) → ℝ≥0 := fun l => (GlobalTheory.Doubling.absEv F E v (φ l))⁻¹ with hf
  have hfc : Continuous f :=
    ((GlobalTheory.Doubling.continuous_absEv v).comp φ.continuous).inv₀ fun l => hne _
  have hfm : ∀ x y, f (x * y) = f x * f y := fun x y => by
    simp only [hf, map_mul, mul_inv]
  have hf1 : ∀ a, f a⁻¹ * f a = 1 := fun a => by
    rw [← hfm, inv_mul_cancel]
    simp [hf]
  haveI : IsLocallyFiniteMeasure ν := by
    refine ⟨fun x => ?_⟩
    obtain ⟨s, hs, hs'⟩ := lam.finiteAt_nhds (j x)
    refine ⟨j ⁻¹' s, hoe.continuous.continuousAt.preimage_mem_nhds hs, ?_⟩
    rw [hνa]
    exact (measure_mono (Set.image_preimage_subset _ _)).trans_lt hs'
  haveI : ν.IsOpenPosMeasure := by
    refine ⟨fun U hU hn => ?_⟩
    rw [hνa]
    exact (hoe.isOpenMap U hU).measure_ne_zero lam (hn.image _)
  haveI := IsLocallyFiniteMeasure.withDensity_coe (μ := ν) hfc
  have hpos : (ν.withDensity fun x => (f x : ℝ≥0∞)).IsOpenPosMeasure := by
    refine (withDensity_absolutelyContinuous' (μ := ν)
      (hfc.measurable.coe_nnreal_ennreal.aemeasurable) ?_).isOpenPosMeasure
    exact Eventually.of_forall fun x => ENNReal.coe_ne_zero.2 (inv_ne_zero (hne _))
  have hinv : (ν.withDensity fun x => (f x : ℝ≥0∞)).IsMulLeftInvariant := by
    refine ⟨fun a => ?_⟩
    have hma : MeasurableEmbedding (fun x : idelesAt E (evFin F v) => a * x) :=
      (Homeomorph.mulLeft a).measurableEmbedding
    have hmap : Measure.map (fun x : idelesAt E (evFin F v) => a * x) ν = (f a : ℝ≥0∞) • ν := by
      ext s hs
      rw [hma.map_apply, Measure.smul_apply, hνa, hνa, smul_eq_mul]
      have e : j '' ((fun x => a * x) ⁻¹' s) = (φ a)⁻¹ • (j '' s) := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          refine ⟨j (a * x), ⟨a * x, hx, rfl⟩, ?_⟩
          simp [j, Units.smul_def, map_mul]
        · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
          refine ⟨a⁻¹ * x, by simpa using hx, ?_⟩
          simp [j, Units.smul_def, map_mul, map_inv]
      rw [e, ← distribHaarChar_mul lam (φ a)⁻¹ (j '' s), map_inv, distribHaarChar_Ev]
      rfl
    ext s hs
    rw [hma.map_apply, withDensity_apply _ (hma.measurable hs), withDensity_apply _ hs]
    have h1 : ∀ x, (f x : ℝ≥0∞) = (f a⁻¹ : ℝ≥0∞) * (f (a * x) : ℝ≥0∞) := fun x => by
      rw [← ENNReal.coe_mul, hfm, ← mul_assoc, hf1, one_mul]
    have h2 : (f a⁻¹ : ℝ≥0∞) * (f a : ℝ≥0∞) = 1 := by
      rw [← ENNReal.coe_mul, hf1, ENNReal.coe_one]
    calc ∫⁻ x in (fun x => a * x) ⁻¹' s, (f x : ℝ≥0∞) ∂ν
        = ∫⁻ x in (fun x => a * x) ⁻¹' s, (f a⁻¹ : ℝ≥0∞) * (f (a * x) : ℝ≥0∞) ∂ν := lintegral_congr h1
      _ = (f a⁻¹ : ℝ≥0∞) * ∫⁻ x in (fun x => a * x) ⁻¹' s, (f (a * x) : ℝ≥0∞) ∂ν :=
          lintegral_const_mul' _ _ ENNReal.coe_ne_top
      _ = (f a⁻¹ : ℝ≥0∞) * ∫⁻ x in s, (f x : ℝ≥0∞) ∂(Measure.map (fun x => a * x) ν) := by
          rw [hma.restrict_map, hma.lintegral_map]
      _ = _ := by
          rw [hmap, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, ← mul_assoc, h2, one_mul]
  set ρ := ν.withDensity fun x => (f x : ℝ≥0∞) with hρ
  haveI : ρ.IsHaarMeasure := ⟨⟩
  obtain ⟨c, -, hc⟩ := haar_idelesAt_eq_smul μ ρ
  rw [hc]
  refine Integrable.smul_measure ?_ ENNReal.coe_ne_top
  set g : idelesAt E (evFin F v) → ℝ := fun l => ((GlobalTheory.Doubling.absEv F E v (φ l) : ℝ)) ^ z with hg
  have hfun : (fun l : idelesAt E (evFin F v) =>
      C.indicator (fun _ => ((GlobalTheory.Doubling.absE F E l.1 : ℝ)) ^ z) (compFin F E v l.1)) = (j ⁻¹' C).indicator g := by
    funext l
    by_cases h : j l ∈ C
    · rw [Set.indicator_of_mem (show compFin F E v l.1 ∈ C from h), Set.indicator_of_mem (show l ∈ j ⁻¹' C from h),
        absE_of_mem l.2]
      rfl
    · rw [Set.indicator_of_notMem (show compFin F E v l.1 ∉ C from h),
        Set.indicator_of_notMem (show l ∉ j ⁻¹' C from h)]
  rw [hfun]
  have hCm : MeasurableSet (j ⁻¹' C) := hme.measurable hC.isClosed.measurableSet
  have hgc : Continuous g :=
    (NNReal.continuous_coe.comp ((GlobalTheory.Doubling.continuous_absEv v).comp φ.continuous)).pow z
  have hhm : Measurable ((j ⁻¹' C).indicator g) := hgc.measurable.indicator hCm
  refine ⟨hhm.aestronglyMeasurable, ?_⟩
  have hNc : Continuous fun x : Fv F v ⊗[F] E => ‖Algebra.norm (Fv F v) x‖₊ :=
    (GlobalTheory.Doubling.continuous_norm_tens (F := F) (E := E) (R := Fv F v)).nnnorm
  obtain ⟨M, hM⟩ := (hC.image hNc).bddAbove
  have hb : ∀ l, (f l : ℝ≥0∞) * ‖(j ⁻¹' C).indicator g l‖ₑ ≤ (j ⁻¹' C).indicator (fun _ => ((M ^ (z - 1) : ℝ≥0) : ℝ≥0∞)) l := by
    intro l
    by_cases h : l ∈ j ⁻¹' C
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      set a := GlobalTheory.Doubling.absEv F E v (φ l) with ha
      have ha0 : a ≠ 0 := hne _
      have haM : a ≤ M := hM ⟨j l, h, rfl⟩
      have e1 : ‖g l‖ₑ = ((a ^ z : ℝ≥0) : ℝ≥0∞) := by simp [hg, ← ha]
      rw [e1, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
      have e2 : f l * a ^ z = a ^ (z - 1) := by
        rw [show f l = a⁻¹ from rfl, ← mul_pow_sub_one (show z ≠ 0 by omega) a, inv_mul_cancel_left₀ ha0]
      rw [e2]
      exact pow_le_pow_left₀ zero_le haM _
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
      simp
  show ∫⁻ l, ‖(j ⁻¹' C).indicator g l‖ₑ ∂ρ < ⊤
  rw [hρ, lintegral_withDensity_eq_lintegral_mul _ hfc.measurable.coe_nnreal_ennreal hhm.enorm]
  calc ∫⁻ l, ((fun x => (f x : ℝ≥0∞)) * fun l => ‖(j ⁻¹' C).indicator g l‖ₑ) l ∂ν
      ≤ ∫⁻ l, (j ⁻¹' C).indicator (fun _ => ((M ^ (z - 1) : ℝ≥0) : ℝ≥0∞)) l ∂ν := lintegral_mono hb
    _ = ((M ^ (z - 1) : ℝ≥0) : ℝ≥0∞) * ν (j ⁻¹' C) := lintegral_indicator_const hCm _
    _ < ⊤ := by
      refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
      rw [hνa]
      exact (measure_mono (Set.image_preimage_subset _ _)).trans_lt hC.measure_lt_top

end GlobalTheory.LocTateInt
end
end

