import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0262
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0034
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0260
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0257
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0263

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CokernelSectionIdealPower
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.PowImage

lemma idealSumMap_comp_natural {A : Type} [CommRing A] [IsNoetherianRing A] {Z : Scheme.{0}}
    [Z.Over (Spec (.of A))] {F G : Z.Modules} (g : F ⟶ G) (J : Ideal A) :
    idealSumMap F J ≫ g = biproduct.map (fun _ => g) ≫ idealSumMap G J := by
  apply biproduct.hom_ext'
  intro k
  simp only [idealSumMap, biproduct.ι_desc_assoc, biproduct.ι_map_assoc, smulHom_comp,
    biproduct.ι_desc]

lemma idealPowι_comp_cokernel {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {Z : Scheme.{0}} [Z.Over (Spec (.of A))] {F G : Z.Modules} (g : F ⟶ G) (m : ℕ) :
    idealPowι I F m ≫ g ≫ cokernel.π (idealSumMap G (I ^ m)) = 0 := by
  apply (cancel_epi (Abelian.factorThruImage (idealSumMap F (I ^ m)))).1
  have hfac : Abelian.factorThruImage (idealSumMap F (I ^ m)) ≫
      kernel.ι (cokernel.π (idealSumMap F (I ^ m))) = idealSumMap F (I ^ m) :=
    Abelian.image.fac _
  rw [comp_zero, ← Category.assoc, hfac, ← Category.assoc, idealSumMap_comp_natural,
    Category.assoc, cokernel.condition, comp_zero]

theorem adjMap_app_mem_range_idealPowι {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X Z : Scheme.{0}} [Z.Over (Spec (.of A))] (φ : Z ⟶ X) {E : X.Modules} (S : ℕ → Subobject E)
    (B : Subobject ((Scheme.Modules.pullback φ).obj E)) (n : ℕ)
    (hB : B ⊔ powSub I _ (n + 1) = pullSys I φ E S n) (V : X.Opens) (x : Γ(E, V))
    (hx : x ∈ secs (S n) V) :
    (show Γ(cokernel B.arrow, φ ⁻¹ᵁ V) from (adjMap φ B).app V x) ∈
      Set.range ((idealPowι I (cokernel B.arrow) (n + 1)).app (φ ⁻¹ᵁ V)) := by
  obtain ⟨y, rfl⟩ := hx
  let f := cokernel.π B.arrow ≫ cokernel.π (idealSumMap (cokernel B.arrow) (I ^ (n + 1)))
  have hle : pullSys I φ E S n ≤ kernelSubobject f := by
    rw [← hB]
    refine sup_le ?_ ?_
    · apply le_kernelSubobject
      rw [← Category.assoc, cokernel.condition, zero_comp]
    · apply le_kernelSubobject
      rw [powSub, ← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc,
        idealPowι_comp_cokernel, comp_zero]
  have hS : (Scheme.Modules.pullback φ).map (S n).arrow ≫ f = 0 := by
    have h1 := le_sup_left.trans hle
    rw [← imageSubobject_arrow_comp ((Scheme.Modules.pullback φ).map (S n).arrow), Category.assoc,
      ← Subobject.ofLE_arrow h1, Category.assoc, kernelSubobject_arrow_comp, comp_zero, comp_zero]
  let k := kernel.lift (cokernel.π (idealSumMap (cokernel B.arrow) (I ^ (n + 1))))
    ((Scheme.Modules.pullback φ).map (S n).arrow ≫ cokernel.π B.arrow)
    (by rw [Category.assoc]; exact hS)
  have hk : k ≫ idealPowι I (cokernel B.arrow) (n + 1) =
      (Scheme.Modules.pullback φ).map (S n).arrow ≫ cokernel.π B.arrow := kernel.lift_ι _ _ _
  have hadj : (S n).arrow ≫ adjMap φ B =
      (Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app _ ≫
        (Scheme.Modules.pushforward φ).map (k ≫ idealPowι I (cokernel B.arrow) (n + 1)) := by
    rw [adjMap, Adjunction.homEquiv_unit, hk, Functor.map_comp, ← Category.assoc, ← Category.assoc]
    congr 1
    exact (Scheme.Modules.pullbackPushforwardAdjunction φ).unit.naturality (S n).arrow
  refine ⟨((Scheme.Modules.pushforward φ).map k).app V
    (((Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app _).app V y), ?_⟩
  have h2 := congrArg (fun g => g.app V y) hadj
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, Functor.map_comp] at h2
  rw [h2]
  rfl

end GlobalTheory.CompanionTheory.GE.PowImage
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompleteModuleNoetherianRealization
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.CompletionTower

open AdicCompletion

variable {B : Type} [CommRing B] (I : Ideal B) {N : Type} [AddCommGroup N] [Module B N]

theorem exists_eval_smul (r : AdicCompletion I B) (x : AdicCompletion I N) (n : ℕ) :
    ∃ b : B, eval I N n (r • x) = b • eval I N n x := by
  obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (r.val n)
  exact ⟨b, by show (r • x).val n = b • x.val n; rw [smul_eval, ← hb]; rfl⟩

theorem finite_adicCompletion [Module.Finite B N] :
    Module.Finite (AdicCompletion I B) (AdicCompletion I N) :=
  Module.Finite.of_surjective (ofTensorProduct I N) (ofTensorProduct_surjective_of_finite I N)

theorem span_range_of [Module.Finite B N] :
    Submodule.span (AdicCompletion I B) (Set.range (of I N)) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun x ↦ ?_
  obtain ⟨t, rfl⟩ := ofTensorProduct_surjective_of_finite I N x
  induction t with
  | zero => simp
  | tmul a e =>
    rw [ofTensorProduct_tmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, rfl⟩)
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

variable {I} (T : ℕ → Submodule B N) (hT : ∀ n, I ^ (n + 1) • (⊤ : Submodule B N) ≤ T n)

noncomputable def toQuot (n : ℕ) : AdicCompletion I N →ₗ[B] N ⧸ T n :=
  Submodule.factor (hT n) ∘ₗ eval I N (n + 1)

theorem toQuot_of (n : ℕ) (e : N) : toQuot T hT n (of I N e) = (T n).mkQ e := by
  simp [toQuot, eval_of, Submodule.factor_mk]

theorem toQuot_mk (n : ℕ) (f : AdicCauchySequence I N) :
    toQuot T hT n (AdicCompletion.mk I N f) = (T n).mkQ (f (n + 1)) := by
  show Submodule.factor (hT n) ((AdicCompletion.mk I N f).val (n + 1)) = _
  rw [mk_apply_coe, Submodule.factor_mk]

noncomputable def Tb (n : ℕ) : Submodule (AdicCompletion I B) (AdicCompletion I N) where
  carrier := {x | toQuot T hT n x = 0}
  add_mem' {x y} hx hy := by simp_all
  zero_mem' := by simp
  smul_mem' r x hx := by
    obtain ⟨b, hb⟩ := exists_eval_smul I r x (n + 1)
    have : toQuot T hT n (r • x) = b • toQuot T hT n x := by
      simp only [toQuot, LinearMap.comp_apply, hb, map_smul]
    simp_all

theorem mem_Tb (n : ℕ) (x : AdicCompletion I N) : x ∈ Tb T hT n ↔ toQuot T hT n x = 0 := Iff.rfl

theorem antitone_of_eq_sup_pow_smul_whole_module (hT' : ∀ n, T n = T (n + 1) ⊔ I ^ (n + 1) • (⊤ : Submodule B N)) : Antitone T :=
  antitone_nat_of_succ_le fun n ↦ (hT' n).symm ▸ le_sup_left

theorem exists_lift (hT' : ∀ n, T n = T (n + 1) ⊔ I ^ (n + 1) • (⊤ : Submodule B N)) (n : ℕ) (e : N)
    (he : e ∈ T n) : ∃ l ∈ ⨅ m, Tb T hT m, eval I N (n + 1) l = eval I N (n + 1) (of I N e) := by
  have step : ∀ j (x : T (n + j)), ∃ y : T (n + j + 1),
      (x : N) - y ∈ I ^ (n + j + 1) • (⊤ : Submodule B N) := by
    intro j x
    have hx : (x : N) ∈ T (n + j + 1) ⊔ I ^ (n + j + 1) • (⊤ : Submodule B N) := by
      rw [← hT']; exact x.2
    obtain ⟨a, ha, c, hc, hxe⟩ := Submodule.mem_sup.1 hx
    exact ⟨⟨a, ha⟩, by rw [← hxe]; simpa using hc⟩
  choose f hf using step
  let u : (j : ℕ) → T (n + j) := fun j ↦ Nat.rec ⟨e, he⟩ (fun j x ↦ f j x) j
  have huj : ∀ j, (u (j + 1)).1 = (f j (u j)).1 := fun j ↦ rfl
  have hu : ∀ j, ((u j).1 - (u (j + 1)).1) ∈ I ^ (n + j + 1) • (⊤ : Submodule B N) := fun j ↦ by
    rw [huj]; exact hf j (u j)
  let s : ℕ → N := fun k ↦ (u (k - (n + 1))).1
  have huc : ∀ a b, a = b → (u a).1 = (u b).1 := by rintro a b rfl; rfl
  have hs0 : ∀ k, k ≤ n + 1 → s k = e := fun k hk ↦ huc _ 0 (Nat.sub_eq_zero_of_le hk)
  have hs1 : ∀ j, s (n + 1 + j) = (u j).1 := fun j ↦ huc _ _ (by omega)
  have hcau : ∀ k, s k ≡ s (k + 1) [SMOD (I ^ k • ⊤ : Submodule B N)] := by
    intro k
    rw [SModEq.sub_mem]
    rcases Nat.lt_or_ge k (n + 1) with hk | hk
    · rw [hs0 k hk.le, hs0 (k + 1) hk, sub_self]; exact zero_mem _
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
      rw [hs1, show n + 1 + j + 1 = n + 1 + (j + 1) by omega, hs1]
      simpa [show n + 1 + j = n + j + 1 by omega] using hu j
  let F : AdicCauchySequence I N := AdicCauchySequence.mk I N s hcau
  have hF : ∀ k, F k = s k := fun k ↦ rfl
  refine ⟨AdicCompletion.mk I N F, Submodule.mem_iInf _ |>.2 fun m ↦ ?_, ?_⟩
  · rw [mem_Tb, toQuot_mk, hF, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rcases Nat.lt_or_ge m n with hm | hm
    · rw [hs0 _ (by omega)]; exact antitone_of_eq_sup_pow_smul_whole_module T hT' hm.le he
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
      rw [show n + j + 1 = n + 1 + j by omega, hs1]; exact (u j).2
  · show (AdicCompletion.mk I N F).val (n + 1) = _
    rw [mk_apply_coe, eval_of, hF, hs0 _ le_rfl]

end GlobalTheory.CompanionTheory.GE.CompletionTower

namespace GlobalTheory.CompanionTheory.GE.CompletionTower

open AdicCompletion

theorem exists_completion_tower : ∀ {B : Type} [CommRing B] [IsNoetherianRing B] (I : Ideal B)
    {N : Type} [AddCommGroup N] [Module B N] [Module.Finite B N] (T : ℕ → Submodule B N),
    (∀ n, I ^ (n + 1) • (⊤ : Submodule B N) ≤ T n) →
    (∀ n, T n = T (n + 1) ⊔ I ^ (n + 1) • (⊤ : Submodule B N)) →
    ∃ (R : Type) (_ : CommRing R) (_ : IsNoetherianRing R) (_ : Algebra B R) (M : Type)
      (_ : AddCommGroup M) (_ : Module R M) (_ : Module B M) (_ : IsScalarTower B R M)
      (_ : Module.Finite R M) (μ : N →ₗ[B] M), I.map (algebraMap B R) ≤ Ideal.jacobson ⊥ ∧
      Submodule.span R (Set.range μ) = ⊤ ∧
      ∀ n e, e ∈ T n ↔ μ e ∈ (I ^ (n + 1) • ⊤ : Submodule B M) := by
  intro B _ _ I N _ _ _ T hT hT'
  haveI := finite_adicCompletion I (N := N)
  haveI := AdicCompletion.isAdicComplete_self I I.fg_of_isNoetherianRing
  let L : Submodule (AdicCompletion I B) (AdicCompletion I N) := ⨅ m, Tb T hT m
  let μ : N →ₗ[B] AdicCompletion I N ⧸ L := (L.mkQ.restrictScalars B) ∘ₗ of I N
  refine ⟨AdicCompletion I B, inferInstance, GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion B I,
    inferInstance, AdicCompletion I N ⧸ L, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, μ, IsAdicComplete.le_jacobson_bot _, ?_, ?_⟩
  · have : Set.range μ = L.mkQ '' Set.range (of I N) := by
      ext y; simp [μ]
    rw [this, ← Submodule.map_span, span_range_of, Submodule.map_top, Submodule.range_mkQ]
  · intro n e
    constructor
    · intro he
      obtain ⟨l, hl, hle⟩ := exists_lift T hT hT' n e he
      have hmem : of I N e - l ∈ (I ^ (n + 1) • ⊤ : Submodule B (AdicCompletion I N)) := by
        rw [AdicCompletion.pow_smul_top_eq_ker_eval I.fg_of_isNoetherianRing, LinearMap.mem_ker,
          map_sub, hle, sub_self]
      have hl0 : L.mkQ l = 0 := (Submodule.Quotient.mk_eq_zero L).2 hl
      have hμ : μ e = (L.mkQ.restrictScalars B) (of I N e - l) := by
        simp only [μ, LinearMap.comp_apply, LinearMap.restrictScalars_apply, map_sub, hl0, sub_zero]
      have h2 := Submodule.mem_map_of_mem (f := L.mkQ.restrictScalars B) hmem
      rw [Submodule.map_smul''] at h2
      rw [hμ]
      exact Submodule.smul_mono le_rfl le_top h2
    · intro hμ
      have key : (I ^ (n + 1) • ⊤ : Submodule B (AdicCompletion I N ⧸ L)) ≤
          (LinearMap.ker (toQuot T hT n)).map (L.mkQ.restrictScalars B) := by
        rw [Submodule.smul_le]
        intro i hi m _
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective L m
        refine ⟨i • x, ?_, by simp⟩
        show toQuot T hT n (i • x) = 0
        rw [map_smul]
        obtain ⟨y, hy⟩ := Submodule.mkQ_surjective (T n) (toQuot T hT n x)
        rw [← hy, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hT n (Submodule.smul_mem_smul hi Submodule.mem_top)
      obtain ⟨x, hx, hxe⟩ := key hμ
      have hd : x - of I N e ∈ L := (Submodule.Quotient.eq L).1 hxe
      have hd' := (Submodule.mem_iInf _).1 hd n
      rw [mem_Tb, map_sub, LinearMap.mem_ker.1 hx, zero_sub, neg_eq_zero, toQuot_of,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hd'
      exact hd'

end GlobalTheory.CompanionTheory.GE.CompletionTower
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeFrameEmbedding
section
noncomputable section

open Formalism.UG Matrix

namespace GlobalTheory.CompanionTheory.PlaneSA.OfTwo

section Ring

variable {S : Type} [CommRing S] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def emb0 (V : Matrix m n S) (P : Matrix n m S) (x : Matrix n n S) : Matrix m m S :=
  1 + V * (x - 1) * P

structure IsFrame (c : S →+* S) (J : Matrix m m S) (K : Matrix n n S) (a : S) (V : Matrix m n S)
    (P : Matrix n m S) : Prop where
  pv : P * V = 1
  jv : J * V = a • (cT c P * K)
  vj : cT c V * J = a • (K * P)

theorem cT_add (c : S →+* S) {p q : Type} (X Y : Matrix p q S) : cT c (X + Y) = cT c X + cT c Y := by
  ext i j; simp [cT]

theorem cT_sub (c : S →+* S) {p q : Type} (X Y : Matrix p q S) : cT c (X - Y) = cT c X - cT c Y := by
  ext i j; simp [cT]

theorem frame_embedding_one (V : Matrix m n S) (P : Matrix n m S) : emb0 V P 1 = 1 := by simp [emb0]

theorem embed_mul {V : Matrix m n S} {P : Matrix n m S} (h : P * V = 1) (x y : Matrix n n S) :
    emb0 V P (x * y) = emb0 V P x * emb0 V P y := by
  have e : V * (x - 1) * P * (V * (y - 1) * P) = V * ((x - 1) * (y - 1)) * P := by
    calc V * (x - 1) * P * (V * (y - 1) * P) = V * (x - 1) * (P * V) * (y - 1) * P := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  simp only [emb0, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, e]
  have e2 : x * y - 1 = (x - 1) * (y - 1) + (x - 1) + (y - 1) := by noncomm_ring
  rw [e2]
  simp only [Matrix.mul_add, Matrix.add_mul]
  abel

def embHom {V : Matrix m n S} {P : Matrix n m S} (h : P * V = 1) : Matrix n n S →* Matrix m m S where
  toFun := emb0 V P
  map_one' := frame_embedding_one V P
  map_mul' := embed_mul h

theorem det_frame_embedding {V : Matrix m n S} {P : Matrix n m S} (h : P * V = 1) (x : Matrix n n S) :
    (emb0 V P x).det = x.det := by
  have e : emb0 V P x = 1 + V * ((x - 1) * P) := by rw [emb0, Matrix.mul_assoc]
  rw [e, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, h, Matrix.mul_one]
  simp

theorem projection_frame_embedding {V : Matrix m n S} {P : Matrix n m S} (h : P * V = 1) (x : Matrix n n S) :
    P * emb0 V P x * V = x := by
  have e : P * (1 + V * (x - 1) * P) * V = P * V + (P * V) * (x - 1) * (P * V) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [emb0, e, h]
  simp

theorem conj_transpose_frame_embedding (c : S →+* S) (V : Matrix m n S) (P : Matrix n m S) (x : Matrix n n S) :
    cT c (emb0 V P x) = 1 + cT c P * (cT c x - 1) * cT c V := by
  rw [emb0, cT_add, cT_one, cT_mul, cT_mul, cT_sub, cT_one, Matrix.mul_assoc]

theorem frame_embedding_form_defect {c : S →+* S} {J : Matrix m m S} {K : Matrix n n S} {a : S} {V : Matrix m n S}
    {P : Matrix n m S} (h : IsFrame c J K a V P) (x : Matrix n n S) :
    cT c (emb0 V P x) * J * emb0 V P x = J + a • (cT c P * (cT c x * K * x - K) * P) := by
  have hvjv : cT c V * J * V = a • K := by
    rw [h.vj, Matrix.smul_mul, Matrix.mul_assoc, h.pv, Matrix.mul_one]
  set A := x - 1 with hA
  set B := cT c x - 1 with hB
  have hx : x = A + 1 := by rw [hA]; abel
  have hcx : cT c x = B + 1 := by rw [hB]; abel
  have e1 : cT c x * K * x - K = K * A + B * K + B * K * A := by
    rw [hcx, hx]; noncomm_ring
  have t1 : J * (V * A * P) = a • (cT c P * (K * A) * P) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h.jv]
    simp only [Matrix.smul_mul, Matrix.mul_assoc]
  have t2 : cT c P * B * cT c V * J = a • (cT c P * (B * K) * P) := by
    rw [Matrix.mul_assoc _ (cT c V) J, h.vj]
    simp only [Matrix.mul_smul, Matrix.mul_assoc]
  have t3 : cT c P * B * cT c V * J * (V * A * P) = a • (cT c P * (B * K * A) * P) := by
    calc cT c P * B * cT c V * J * (V * A * P) = cT c P * B * (cT c V * J * V) * A * P := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hvjv]
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [conj_transpose_frame_embedding, ← hB, emb0, ← hA, e1]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, smul_add]
  rw [t3, t2, t1]
  abel

theorem frame_embedding_unitary {c : S →+* S} {J : Matrix m m S} {K : Matrix n n S} {a : S} {V : Matrix m n S}
    {P : Matrix n m S} (h : IsFrame c J K a V P) {x : Matrix n n S} (hx : cT c x * K * x = K) :
    cT c (emb0 V P x) * J * emb0 V P x = J := by
  rw [frame_embedding_form_defect h, hx]; simp

theorem unitary_of_frame_embedding {c : S →+* S} {J : Matrix m m S} {K : Matrix n n S} {a b : S} {V : Matrix m n S}
    {P : Matrix n m S} (h : IsFrame c J K a V P) (hab : b * a = 1) {x : Matrix n n S}
    (hx : cT c (emb0 V P x) * J * emb0 V P x = J) : cT c x * K * x = K := by
  rw [frame_embedding_form_defect h] at hx
  have h0 : a • (cT c P * (cT c x * K * x - K) * P) = 0 := by simpa using hx
  have hvp : cT c V * cT c P = 1 := by rw [← cT_mul, h.pv, cT_one]
  have h1 : a • (cT c x * K * x - K) = 0 := by
    have := congrArg (fun Y => cT c V * Y * V) h0
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_zero, Matrix.zero_mul] at this
    have e : cT c V * (cT c P * (cT c x * K * x - K) * P) * V =
        (cT c V * cT c P) * (cT c x * K * x - K) * (P * V) := by simp only [Matrix.mul_assoc]
    rwa [e, hvp, h.pv, Matrix.one_mul, Matrix.mul_one] at this
  have h2 : cT c x * K * x - K = 0 := by
    have := congrArg (fun Y => b • Y) h1
    simpa [smul_smul, hab] using this
  exact sub_eq_zero.1 h2

theorem fix_left {c : S →+* S} {J : Matrix m m S} {K : Matrix n n S} {a : S} {V : Matrix m n S}
    {P : Matrix n m S} (h : IsFrame c J K a V P) {L : Matrix m m S} (hL : L * J = 1) {g : Matrix m m S}
    (hg : cT c g * J * g = J) (hq : g * (1 - V * P) = 1 - V * P) : (1 - V * P) * g = 1 - V * P := by
  set q := 1 - V * P with hqd
  have hsym : cT c q * J = J * q := by
    have e1 : cT c q = 1 - cT c P * cT c V := by rw [hqd, cT_sub, cT_one, cT_mul]
    rw [e1, Matrix.sub_mul, Matrix.one_mul, hqd, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, h.vj,
      ← Matrix.mul_assoc J, h.jv]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  have hstar : cT c q * cT c g = cT c q := by rw [← cT_mul, hq]
  have h1 : J * q * g = J * q := by
    rw [← hsym]
    calc cT c q * J * g = cT c q * cT c g * J * g := by rw [hstar]
      _ = cT c q * (cT c g * J * g) := by simp only [Matrix.mul_assoc]
      _ = cT c q * J := by rw [hg]
  calc q * g = L * (J * q * g) := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hL, Matrix.one_mul]
    _ = q := by rw [h1, ← Matrix.mul_assoc, hL, Matrix.one_mul]

theorem frame_embedding_projection {V : Matrix m n S} {P : Matrix n m S} (h : P * V = 1) {g : Matrix m m S}
    (h1 : g * (1 - V * P) = 1 - V * P) (h2 : (1 - V * P) * g = 1 - V * P) :
    emb0 V P (P * g * V) = g := by
  set p := V * P with hp
  have hpp : p * p = p := by
    calc p * p = V * (P * V) * P := by simp only [hp, Matrix.mul_assoc]
      _ = p := by rw [h, Matrix.mul_one]
  have a1 : g * p = g - 1 + p := by
    have : g - g * p = 1 - p := by rw [← h1, Matrix.mul_sub, Matrix.mul_one]
    rw [show g * p = g - (g - g * p) by abel, this]; abel
  have a2 : p * g = g - 1 + p := by
    have : g - p * g = 1 - p := by rw [← h2, Matrix.sub_mul, Matrix.one_mul]
    rw [show p * g = g - (g - p * g) by abel, this]; abel
  have e : V * (P * g * V - 1) * P = p * g * p - p := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hp]
    simp only [Matrix.mul_assoc]
  rw [emb0, e, a2, Matrix.add_mul, Matrix.sub_mul, a1, hpp, Matrix.one_mul]
  abel

theorem IsFrame.map {S' : Type} [CommRing S'] {c : S →+* S} {c' : S' →+* S'} (f : S →+* S')
    (hf : ∀ s, f (c s) = c' (f s)) {J : Matrix m m S} {K : Matrix n n S} {a : S} {V : Matrix m n S}
    {P : Matrix n m S} (h : IsFrame c J K a V P) :
    IsFrame c' (J.map f) (K.map f) (f a) (V.map f) (P.map f) := by
  have hc : ∀ {p q : Type} (X : Matrix p q S), cT c' (X.map f) = (cT c X).map f := by
    intro p q X; ext i j; simp [cT, hf]
  have hm : ∀ {p q r : Type} [Fintype q] (X : Matrix p q S) (Y : Matrix q r S),
      X.map f * Y.map f = (X * Y).map f := fun X Y => (Matrix.map_mul (f := f)).symm
  have hs : ∀ {p q : Type} (X : Matrix p q S), f a • X.map f = (a • X).map f := by
    intro p q X; ext i j; simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hm, h.pv]; simp [Matrix.map_one]
  · rw [hm, h.jv, hc, hm, hs]
  · rw [hc, hm, h.vj, hm, hs]

theorem frame_embedding_map {S' : Type} [CommRing S'] (f : S →+* S') (V : Matrix m n S) (P : Matrix n m S)
    (x : Matrix n n S) : (emb0 V P x).map f = emb0 (V.map f) (P.map f) (x.map f) := by
  have h1 : ∀ {k : Type} [DecidableEq k], (1 : Matrix k k S).map f = 1 := fun {k} _ =>
    Matrix.map_one f (map_zero f) (map_one f)
  have hm : ∀ {p q r : Type} [Fintype q] (X : Matrix p q S) (Y : Matrix q r S),
      (X * Y).map f = X.map f * Y.map f := fun X Y => Matrix.map_mul (f := f)
  have hs : (x - 1).map f = x.map f - 1 := by
    have : (x - 1).map f = x.map f - (1 : Matrix n n S).map f := by
      ext i j; simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]
    rw [this, h1]
  have ha : ∀ X Y : Matrix m m S, (X + Y).map f = X.map f + Y.map f := fun X Y => by
    ext i j; simp
  rw [emb0, emb0, ha, h1, hm, hm, hs]

end Ring

end GlobalTheory.CompanionTheory.PlaneSA.OfTwo

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenseVectorPairTwoPlaces
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem exists_tensCoord (K : Type) [NontriviallyNormedField K] [Algebra F K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι F E) :
    ∃ ψ : (ι → K) → K ⊗[F] E, Continuous ψ ∧ Function.Surjective ψ ∧
      ∀ c : ι → F, ψ (fun i => algebraMap F K (c i)) = inclR K (∑ i, c i • b i) := by
  haveI : IsModuleTopology K (K ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (K ⊗[F] E) := IsModuleTopology.toContinuousAdd K (K ⊗[F] E)
  haveI : ContinuousSMul K (K ⊗[F] E) := IsModuleTopology.toContinuousSMul K (K ⊗[F] E)
  let e := (Algebra.TensorProduct.basis K b).equivFun
  refine ⟨e.symm, IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap, e.symm.surjective, fun c => ?_⟩
  change (Algebra.TensorProduct.basis K b).equivFun.symm _ = (1 : K) ⊗ₜ[F] (∑ i, c i • b i)
  rw [Module.Basis.equivFun_symm_apply, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one]

theorem denseRange_inclR_pair [FiniteDimensional F E] {K₁ K₂ : Type} [NontriviallyNormedField K₁] [Algebra F K₁]
    [NontriviallyNormedField K₂] [Algebra F K₂]
    (h : DenseRange (fun f : F => (algebraMap F K₁ f, algebraMap F K₂ f))) :
    DenseRange (fun x : E => ((inclR K₁ x, inclR K₂ x) : (K₁ ⊗[F] E) × (K₂ ⊗[F] E))) := by
  classical
  let b := Module.finBasis F E
  obtain ⟨ψ₁, c₁, s₁, h₁⟩ := exists_tensCoord K₁ b
  obtain ⟨ψ₂, c₂, s₂, h₂⟩ := exists_tensCoord K₂ b
  let G : (Fin (Module.finrank F E) → K₁ × K₂) → (K₁ ⊗[F] E) × (K₂ ⊗[F] E) :=
    fun w => (ψ₁ (fun i => (w i).1), ψ₂ (fun i => (w i).2))
  have hGc : Continuous G := (c₁.comp (by fun_prop)).prodMk (c₂.comp (by fun_prop))
  have hGs : Function.Surjective G := by
    rintro ⟨x, y⟩
    obtain ⟨u, rfl⟩ := s₁ x
    obtain ⟨v, rfl⟩ := s₂ y
    exact ⟨fun i => (u i, v i), rfl⟩
  have hD : DenseRange (Pi.map fun (_ : Fin (Module.finrank F E)) (f : F) =>
      (algebraMap F K₁ f, algebraMap F K₂ f)) := DenseRange.piMap fun _ => h
  refine Dense.mono ?_ (hGs.denseRange.comp hD hGc)
  rintro _ ⟨c, rfl⟩
  refine ⟨∑ i, c i • b i, ?_⟩
  exact (Prod.ext (h₁ c) (h₂ c)).symm

end Coord

theorem denseRange_ratPairs : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {K₁ K₂ : Type} [NontriviallyNormedField K₁] [Algebra F K₁] [NontriviallyNormedField K₂] [Algebra F K₂], DenseRange (fun f : F => (algebraMap F K₁ f, algebraMap F K₂ f)) → ∀ M : ℕ, DenseRange (fun p : (Fin M → E) × (Fin M → E) => (((incV K₁ p.1, incV K₁ p.2), (incV K₂ p.1, incV K₂ p.2)) : ((Fin M → K₁ ⊗[F] E) × (Fin M → K₁ ⊗[F] E)) × ((Fin M → K₂ ⊗[F] E) × (Fin M → K₂ ⊗[F] E)))) := by
  intro F E _ _ _ _ _ σ _ K₁ K₂ _ _ _ _ h M
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hP : DenseRange (Pi.map fun (_ : Fin M) (x : E) =>
      ((inclR K₁ x, inclR K₂ x) : (K₁ ⊗[F] E) × (K₂ ⊗[F] E))) :=
    DenseRange.piMap fun _ => denseRange_inclR_pair h
  let g : ((Fin M → (K₁ ⊗[F] E) × (K₂ ⊗[F] E)) × (Fin M → (K₁ ⊗[F] E) × (K₂ ⊗[F] E))) →
      ((Fin M → K₁ ⊗[F] E) × (Fin M → K₁ ⊗[F] E)) × ((Fin M → K₂ ⊗[F] E) × (Fin M → K₂ ⊗[F] E)) :=
    fun q => ((fun i => (q.1 i).1, fun i => (q.2 i).1), (fun i => (q.1 i).2, fun i => (q.2 i).2))
  have hgc : Continuous g := by fun_prop
  have hgs : Function.Surjective g := by
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
    exact ⟨(fun i => (a i, c i), fun i => (b i, d i)), rfl⟩
  exact hgs.denseRange.comp (hP.prodMap hP) hgc

end GlobalTheory.CompanionTheory.SaGen
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealSheafWellFoundedGtStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_sheaf_well_founded_gt : ∀ {X : Scheme.{0}} [IsNoetherian X], WellFoundedGT X.IdealSheafData := by
  first | exact @GlobalTheory.CompanionTheory.GE.idealSheafData_wellFoundedGT | exact GlobalTheory.CompanionTheory.GE.idealSheafData_wellFoundedGT | (intros; apply GlobalTheory.CompanionTheory.GE.idealSheafData_wellFoundedGT <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NoetherianIdealIntegralOrSplitStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noetherian_ideal_integral_or_split : ∀ {X : Scheme.{0}} [IsNoetherian X] (J : X.IdealSheafData), J ≠ ⊤ → IsIntegral J.subscheme ∨ ∃ J₁ J₂ : X.IdealSheafData, J < J₁ ∧ J < J₂ ∧ ∀ (U : X.affineOpens) (a b : Γ(X, U)), a ∈ J₁.ideal U → b ∈ J₂.ideal U → a * b ∈ J.ideal U := by
  first | exact @GlobalTheory.CompanionTheory.GE.Dich.isIntegral_or_exists_mul_mem | exact GlobalTheory.CompanionTheory.GE.Dich.isIntegral_or_exists_mul_mem | (intros; apply GlobalTheory.CompanionTheory.GE.Dich.isIntegral_or_exists_mul_mem <;> assumption)
end

