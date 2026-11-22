import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1809
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1802
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1914
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1744
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1911
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1050

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnLocOpsMemberNonsplit
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped Classical

namespace GlobalTheory.HoweLocal

theorem isContOn_locOps_member_nonsplit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (a b : ℕ)
    (JA : Matrix (Fin a) (Fin a) E) (B : Spc F E b) (κ : Type) [Fintype κ]
    (dA : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F B.J)) κ) (ψ : AddChar (AF F) ℂ)
    (omB : UA σ B.J →* Module.End ℂ ((κ → AF F) → ℂ)),
    IsStd ψ → IsUSplitting (adeleClass F) ψ dA (actB (cA σ)) omB →
    ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) → ∀ [Invertible (2 : Fv F v)],
    ∀ (eB : UAtGrp σ B (evFin F v) ≃* UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v B.J)),
      GlobalTheory.HoweLocal.IsCompIso σ B v eB →
    ∀ omL : UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v B.J) →* Module.End ℂ ((κ → Fv F v) → ℂ),
      (∀ g, ∀ φ ∈ SB (κ → Fv F v), omL g φ ∈ SB (κ → Fv F v) ∧
        Acts (evFin F v) (omB (eB.symm g).1) φ (omL g φ)) →
    ∀ co : Darboux (symp (R := Fv F v) (GlobalTheory.HoweLocal.cv σ v) (-1) (GlobalTheory.HoweLocal.Jv v JA)
        (GlobalTheory.HoweLocal.Jv v B.J)) κ,
      (∀ x, co.e x = GlobalTheory.LatVac.locCo dA v (x.map (GlobalTheory.HoweLocal.liftE v))) →
    IsContOn (sbClass (Fv F v)) omL := by
  intro F E _ _ _ _ _ σ a b JA B κ _ dA ψ omB _ hsp v _ _ eB heB omL hom _ _
  have hcomp : omL = (omL.comp eB.toMonoidHom).comp eB.symm.toMonoidHom := by
    ext g : 1
    simp
  rw [hcomp]
  refine IsContOn.comp ?_ heB.2.2
  intro l _ φ hφ
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  let lift : (κ → Fv F v) → (κ → AF F) := fun t i => GlobalTheory.LatVac.liftV v (t i)
  let L : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ := (R 0)⁻¹ • l.comp (LinearMap.funLeft ℂ ℂ lift)
  have hL : L ∈ (adeleClass F).adm κ := by
    intro g _
    refine ⟨((R 0)⁻¹ * l (fun t => g (fun i => (lift t i).2))) •
      ((BoundedContinuousFunction.evalCLM ℂ 0).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩
    have e : (fun t => pureA F f g (lift t)) = f 0 • fun t => g (fun i => (lift t i).2) := by
      funext t
      have h0 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (lift t i).1) = 0 := by
        funext i
        show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
        exact map_zero _
      simp only [pureA, h0, Pi.smul_apply, smul_eq_mul]
    show (R 0)⁻¹ • l (fun t => pureA F f g (lift t)) = _
    rw [e, map_smul]
    simp [smul_eq_mul, mul_comm, mul_assoc, mul_left_comm]
  have hc0 : IsContOn (adeleClass F) omB := hsp.cont
  have hc := (hc0 L hL _ (hR φ hφ).2).comp
    (continuous_subtype_val (p := (· ∈ UAtGrp σ B (evFin F v))))
  refine hc.congr fun q => ?_
  have hq := (hom (eB q) φ hφ).2 R (hR φ hφ)
  rw [MulEquiv.symm_apply_apply] at hq
  simp only [Function.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [hq]
  have e : (fun t => tens (evFin F v) (omL (eB q) φ) R (lift t)) = R 0 • omL (eB q) φ := by
    funext t
    have hz : At (evFin F v) (lift t) := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
    have hrz : R (lift t) = R 0 := by simpa using (hR φ hφ).1 0 _ hz
    simp only [tens, lift, GlobalTheory.LatVac.evFin_liftV, Pi.smul_apply, smul_eq_mul]
    rw [show (fun i => GlobalTheory.LatVac.liftV v (t i)) = lift t from rfl, hrz, mul_comm]
  show (R 0)⁻¹ • l (fun t => tens (evFin F v) (omL (eB q) φ) R (lift t)) = _
  rw [e, map_smul, smul_smul, inv_mul_cancel₀ hR0, one_smul]

end GlobalTheory.HoweLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnLocOpsNonsplit
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped Classical

namespace GlobalTheory.HoweLocal

theorem isContOn_locOps_nonsplit : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) → ∀ [Invertible (2 : Fv F v)],
      ∀ om' : UAtGrp σ X (evFin F v) × UAtGrp σ W (evFin F v) →* Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ),
        (∀ g h, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), om' (g, h) φ ∈ SB (Fin n × Fin d → Fv F v) ∧
          Acts (evFin F v) (om (g.1, h.1)) φ (om' (g, h) φ)) →
      ∀ (eX : UAtGrp σ X (evFin F v) ≃* UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v X.J)),
        GlobalTheory.HoweLocal.IsCompIso σ X v eX →
      ∀ (eW : UAtGrp σ W (evFin F v) ≃* UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v W.J)),
        GlobalTheory.HoweLocal.IsCompIso σ W v eW →
      ∀ (co : Darboux (symp (R := Fv F v) (GlobalTheory.HoweLocal.cv σ v) (-1) (GlobalTheory.HoweLocal.Jv v X.J) (GlobalTheory.HoweLocal.Jv v W.J))
        (Fin n × Fin d)), GlobalTheory.HoweLocal.IsLocCo σ M v co →
      ∀ χXv χWv : (Fv F v ⊗[F] E)ˣ →* Circle, GlobalTheory.HoweLocal.IsLocChr χX v χXv → GlobalTheory.HoweLocal.IsLocChr χW v χWv →
      IsContOn (sbClass (Fv F v)) (om'.comp (eX.symm.toMonoidHom.prodMap eW.symm.toMonoidHom)) := by
  intro _ F E _ _ _ _ _ σ _ n d X W M ψ χX χW om _ _ _ _ _ _ _ _ _ hWeil v _ _ om' hom' eX heX eW heW _ _ χXv χWv _ _
  refine IsContOn.comp ?_ (f := eX.symm.toMonoidHom.prodMap eW.symm.toMonoidHom) (heX.2.2.prodMap heW.2.2)
  intro l _ φ hφ
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (Fin n × Fin d) v
  let lift : (Fin n × Fin d → Fv F v) → (Fin n × Fin d → AF F) := fun t i => GlobalTheory.LatVac.liftV v (t i)
  let L : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ := (R 0)⁻¹ • l.comp (LinearMap.funLeft ℂ ℂ lift)
  have hL : L ∈ (adeleClass F).adm (Fin n × Fin d) := by
    intro g _
    refine ⟨((R 0)⁻¹ * l (fun t => g (fun i => (lift t i).2))) •
      ((BoundedContinuousFunction.evalCLM ℂ 0).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩
    have e : (fun t => pureA F f g (lift t)) = f 0 • fun t => g (fun i => (lift t i).2) := by
      funext t
      have h0 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (lift t i).1) = 0 := by
        funext i
        show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
        exact map_zero _
      simp only [pureA, h0, Pi.smul_apply, smul_eq_mul]
    show (R 0)⁻¹ • l (fun t => pureA F f g (lift t)) = _
    rw [e, map_smul]
    simp [smul_eq_mul, mul_comm, mul_assoc, mul_left_comm]
  have hc0 : IsContOn (adeleClass F) om := hWeil.2.2
  have hc := (hc0 L hL _ (hR φ hφ).2).comp ((continuous_subtype_val (p := (· ∈ UAtGrp σ X (evFin F v)))).prodMap
    (continuous_subtype_val (p := (· ∈ UAtGrp σ W (evFin F v)))))
  refine hc.congr fun q => ?_
  simp only [Function.comp_apply, Prod.map]
  rw [(hom' q.1 q.2 φ hφ).2 R (hR φ hφ)]
  have e : (fun t => tens (evFin F v) (om' q φ) R (lift t)) = R 0 • om' q φ := by
    funext t
    have hz : At (evFin F v) (lift t) := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
    have hrz : R (lift t) = R 0 := by simpa using (hR φ hφ).1 0 _ hz
    simp only [tens, lift, GlobalTheory.LatVac.evFin_liftV, Pi.smul_apply, smul_eq_mul]
    rw [show (fun i => GlobalTheory.LatVac.liftV v (t i)) = lift t from rfl, hrz, mul_comm]
  show (R 0)⁻¹ • l (fun t => tens (evFin F v) (om' q φ) R (lift t)) = _
  rw [e, map_smul, smul_smul, inv_mul_cancel₀ hR0, one_smul]

end GlobalTheory.HoweLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLocalDarbouxCoordinatesBounded
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000

namespace GlobalTheory.LatVacBdd

theorem exists_ne_zero_mul_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (S : Finset (v.adicCompletion F)) :
    ∃ c : v.adicCompletion F, c ≠ 0 ∧ ∀ a ∈ S, c * a ∈ v.adicCompletionIntegers F := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert b S hb ih =>
    obtain ⟨c, hc0, hc⟩ := ih
    by_cases hcb : c * b ∈ v.adicCompletionIntegers F
    · refine ⟨c, hc0, ?_⟩
      intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact hcb
      · exact hc a ha
    · have hinv : (c * b)⁻¹ ∈ v.adicCompletionIntegers F :=
        ((v.adicCompletionIntegers F).mem_or_inv_mem (c * b)).resolve_left hcb
      have hcb0 : c * b ≠ 0 := fun h => hcb (h ▸ zero_mem _)
      refine ⟨c * (c * b)⁻¹, mul_ne_zero hc0 (inv_ne_zero hcb0), ?_⟩
      intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · rw [mul_assoc, mul_comm _ a, ← mul_assoc, mul_inv_cancel₀ hcb0]; exact one_mem _
      · rw [mul_comm c, mul_assoc]; exact mul_mem hinv (hc a ha)

end GlobalTheory.LatVacBdd

theorem GlobalTheory.LatVacBdd.locCo_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v : Pl F, ∃ c : Fv F v, c ≠ 0 ∧ ∀ γ ∈ latAtV G.V G.W v, ∀ k,
      c * (GlobalTheory.LatVac.locCo G.M.co v γ).1 k ∈ HeightOneSpectrum.adicCompletionIntegers F v ∧
      c * (GlobalTheory.LatVac.locCo G.M.co v γ).2 k ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v
  classical
  choose yf zf hyz using hT.geo.hM.rat
  obtain ⟨sX, hsX⟩ := hT.geo.hV.lat.fg.restrictScalars (R := ℤ)
  obtain ⟨sY, hsY⟩ := hT.geo.hW.lat.fg.restrictScalars (R := ℤ)
  let f : (Fin a → E) →ₗ[ℤ] (Fin (a + a') → E) →ₗ[ℤ] Matrix (Fin a) (Fin (a + a')) E :=
    LinearMap.mk₂ ℤ (fun x y => Matrix.vecMulVec x y)
      (fun x x' y => by ext i j; simp [Matrix.vecMulVec_apply, add_mul])
      (fun c x y => by ext i j; simp [Matrix.vecMulVec_apply, mul_assoc])
      (fun x y y' => by ext i j; simp [Matrix.vecMulVec_apply, mul_add])
      (fun c x y => by ext i j; simp [Matrix.vecMulVec_apply, mul_left_comm])
  let T₀ : Finset (Matrix (Fin a) (Fin (a + a')) E) := Finset.image₂ (fun x y => f x y) sX sY
  have hmem : ∀ x ∈ G.V.L, ∀ y ∈ G.W.L, Matrix.vecMulVec x y ∈ Submodule.span ℤ (T₀ : Set _) := by
    intro x hx y hy
    have hx' : x ∈ Submodule.span ℤ (sX : Set (Fin a → E)) := by
      rw [hsX]; exact hx
    have hy' : y ∈ Submodule.span ℤ (sY : Set (Fin (a + a') → E)) := by
      rw [hsY]; exact hy
    have := Submodule.apply_mem_map₂ f hx' hy'
    rw [Submodule.map₂_span_span] at this
    rw [Finset.coe_image₂]; exact this
  have hgen : latAtV G.V G.W v ≤ AddSubgroup.closure {z | ∃ b : AF F,
      At (evFin F v) b ∧ evFin F v b ∈ v.adicCompletionIntegers F ∧ ∃ t ∈ T₀, z = b • incM F t} := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨b, hb, hbv, x, hx, y, hy, rfl⟩
    let g : Matrix (Fin a) (Fin (a + a')) E →+ Matrix (Fin a) (Fin (a + a')) (AE F E) :=
      (DistribSMul.toAddMonoidHom _ b).comp
        (AddMonoidHom.mapMatrix (inclR (F := F) (E := E) (AF F)).toAddMonoidHom)
    have h1 : Matrix.vecMulVec x y ∈ AddSubgroup.closure (T₀ : Set _) := by
      rw [← Submodule.span_int_eq_addSubgroupClosure]; exact hmem x hx y hy
    have h2 : g (Matrix.vecMulVec x y) ∈ (AddSubgroup.closure (T₀ : Set _)).map g :=
      AddSubgroup.mem_map_of_mem g h1
    rw [AddMonoidHom.map_closure] at h2
    refine AddSubgroup.closure_mono ?_ h2
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨b, hb, hbv, t, ht, rfl⟩
  let S : Finset (Fv F v) :=
    (T₀ ×ˢ (Finset.univ : Finset (Fin a × Fin (a + a')))).image (fun p => algebraMap F (Fv F v) (yf p.1 p.2)) ∪
    (T₀ ×ˢ (Finset.univ : Finset (Fin a × Fin (a + a')))).image (fun p => algebraMap F (Fv F v) (zf p.1 p.2))
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.LatVacBdd.exists_ne_zero_mul_mem v S
  have hcy : ∀ t ∈ T₀, ∀ k, c * algebraMap F (Fv F v) (yf t k) ∈ v.adicCompletionIntegers F := fun t ht k =>
    hc _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨(t, k), Finset.mem_product.2 ⟨ht, Finset.mem_univ _⟩, rfl⟩))
  have hcz : ∀ t ∈ T₀, ∀ k, c * algebraMap F (Fv F v) (zf t k) ∈ v.adicCompletionIntegers F := fun t ht k =>
    hc _ (Finset.mem_union_right _ (Finset.mem_image.2 ⟨(t, k), Finset.mem_product.2 ⟨ht, Finset.mem_univ _⟩, rfl⟩))
  have hev : ∀ y : F, evFin F v (algebraMap F (AF F) y) = algebraMap F (Fv F v) y := fun y => AlgHom.commutes _ _
  refine ⟨c, hc0, fun γ hγ => ?_⟩
  clear_value T₀
  revert hγ
  intro hγ
  have hγ' := hgen hγ
  clear hγ
  induction hγ' using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, -, hbv, t, ht, rfl⟩ := hz
    intro k
    simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearEquiv.map_smul, hyz,
      Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul, hev]
    exact ⟨by rw [mul_left_comm]; exact mul_mem hbv (hcy t ht k),
      by rw [mul_left_comm]; exact mul_mem hbv (hcz t ht k)⟩
  | zero => intro k; simp
  | add x y _ _ hx hy =>
    intro k
    rw [map_add]
    exact ⟨by rw [Prod.fst_add, Pi.add_apply, mul_add]; exact add_mem (hx k).1 (hy k).1,
      by rw [Prod.snd_add, Pi.add_apply, mul_add]; exact add_mem (hx k).2 (hy k).2⟩
  | neg x _ hx =>
    intro k
    rw [map_neg]
    exact ⟨by rw [Prod.fst_neg, Pi.neg_apply, mul_neg]; exact neg_mem (hx k).1,
      by rw [Prod.snd_neg, Pi.neg_apply, mul_neg]; exact neg_mem (hx k).2⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterNormOneUnit
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ChrLocal

open scoped TensorProduct
open GlobalTheory.AdelicU

theorem map_eq_zero_of_at {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {B : Type} [CommRing B]
    [Algebra F B] {v : Pl F} {x : AE F E} (hx : At (evFin F v) x) {a : AF F}
    (ha : evFin F v a = 0) (f : AF F →ₐ[F] B) (hf : f a = 1) :
    Algebra.TensorProduct.map f (AlgHom.id F E) x = 0 := by
  have h := hx a ha
  rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply] at h
  have h2 := congrArg (Algebra.TensorProduct.map f (AlgHom.id F E)) h
  rw [map_mul, Algebra.TensorProduct.map_tmul, map_zero] at h2
  simpa [hf, ← Algebra.TensorProduct.one_def] using h2

theorem eq_locIdele_splitPrime {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {v : Pl F} (τ : E →ₐ[F] Fv F v) (z : (AE F E)ˣ)
    (hz : At (evFin F v) ((z : AE F E) - 1)) (h1 : piW (τ.comp σ) (z : AE F E) = 1) :
    z = GlobalTheory.LFun.locIdele F (splitPrime τ)
      (Units.map (GlobalTheory.LFun.complMap (splitPrime_under τ)).toMonoidHom (Units.map (piW τ).toMonoidHom z)) := by
  refine GlobalTheory.LFun.eq_locIdele ?_ (FiniteAdeleRing.ext _ fun u => ?_)
  · have h := map_eq_zero_of_at hz (a := ((1 : Ainf F), (0 : Af F))) (by
      change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v 0 = 0
      exact map_zero _) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) rfl
    change Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E) (z : AE F E) = 1
    rw [map_sub, map_one, sub_eq_zero] at h
    exact h
  · by_cases hu : u.under (𝓞 F) = v
    · rw [GlobalTheory.LFun.finAdEquiv_apply hu]
      have e : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
          (GlobalTheory.LFun.finTens F E (z : AE F E)) = compFin F E v (z : AE F E) := by
        change Algebra.TensorProduct.map _ (AlgHom.id F E) (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E) _) = _
        rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
        rfl
      rw [e]
      obtain ⟨τ', rfl⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq hσ (GlobalTheory.LFun.SplitChart.isSplit_of_algHom hσ τ) hu
      rw [GlobalTheory.LFun.SplitTie.toCompl_eq_complMap τ' hu]
      change _ = Neutral.B1.finiteSingle E (splitPrime τ) _ (splitPrime τ')
      rcases eq_or_eq_comp_conj hσ τ τ' with rfl | rfl
      · rw [GlobalTheory.LFun.finSingle_self]
        rfl
      · rw [GlobalTheory.LFun.finSingle_ne (splitPrime_comp_ne hσ τ)]
        change GlobalTheory.LFun.complMap hu (piW (τ.comp σ) (z : AE F E)) = 1
        rw [h1, map_one]
    · rw [GlobalTheory.LFun.finAdEquiv_apply rfl]
      have e : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F (u.under (𝓞 F))) (AlgHom.id F E)
          (GlobalTheory.LFun.finTens F E (z : AE F E)) = compFin F E (u.under (𝓞 F)) (z : AE F E) := by
        change Algebra.TensorProduct.map _ (AlgHom.id F E) (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E) _) = _
        rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
        rfl
      have h := map_eq_zero_of_at hz (a := GlobalTheory.LatVac.liftV (u.under (𝓞 F)) 1) (by
        change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (singleFin (u.under (𝓞 F)) 1) = 0
        exact evalV_singleFin_ne (Ne.symm hu) 1) (evFin F (u.under (𝓞 F))) (GlobalTheory.LatVac.evFin_liftV _ 1)
      rw [map_sub, map_one, sub_eq_zero] at h
      have h' : compFin F E (u.under (𝓞 F)) (z : AE F E) = 1 := h
      rw [e, h', map_one]
      change (1 : u.adicCompletion E) = Neutral.B1.finiteSingle E (splitPrime τ) _ u
      exact (GlobalTheory.LFun.finSingle_ne (fun e => hu (by rw [e]; exact splitPrime_under τ)) _).symm

theorem chrW_piW_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (χ : Chr F E) (v : Pl F) (τ : E →ₐ[F] Fv F v) (z : (AE F E)ˣ), At (evFin F v) ((z : AE F E) - 1) →
    piW (τ.comp σ) (z : AE F E) = 1 → chrW χ τ (Units.map (piW τ).toMonoidHom z) = Circle.toUnits (χ z) := by
  intro F E _ _ _ _ _ σ hσ χ v τ z hz h1
  change Circle.toUnits (χ (GlobalTheory.LFun.locIdele F (splitPrime τ) _)) = _
  rw [← eq_locIdele_splitPrime hσ τ z hz h1]

end GlobalTheory.ChrLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormUnramifiedFactorization
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.NormLocSplit

theorem norm_at_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (v : Pl F) (τ : E →ₐ[F] Fv F v) (z : AE F E), At (evFin F v) (z - 1) →
    At (evFin F v) (Algebra.norm (AF F) z - 1) ∧ evFin F v (Algebra.norm (AF F) z) = piW τ z * piW (τ.comp σ) z := by
  intro F E _ _ _ _ _ σ h v τ z hz
  have hN : algebraMap (AF F) (AE F E) (Algebra.norm (AF F) z) = z * cA σ z :=
    GlobalTheory.Doubling.algebraMap_norm_eq h z
  have hinj : Function.Injective (algebraMap (AF F) (AE F E)) :=
    Algebra.TensorProduct.includeLeft_injective (S := AF F) (algebraMap F E).injective
  refine ⟨fun u hu => hinj ?_, ?_⟩
  · have h1 : u • (z - 1) = 0 := hz u hu
    have h2 : u • (cA σ z - 1) = 0 := by
      have := congrArg (cA σ) h1
      rwa [map_smul, map_sub, map_one, map_zero] at this
    rw [smul_eq_mul, map_mul, map_sub, map_one, hN, map_zero, ← Algebra.smul_def,
      show z * cA σ z - 1 = (z - 1) * cA σ z + (cA σ z - 1) by ring, smul_add, ← smul_mul_assoc, h1, h2,
      zero_mul, add_zero]
  · have h3 := congrArg (piW τ) hN
    have hc : piW τ (cA σ z) = piW (τ.comp σ) z := by
      change splitProj τ (compFin F E v (sigR (AF F) σ z)) = splitProj (τ.comp σ) (compFin F E v z)
      have hs : ∀ y : AE F E, compFin F E v (sigR (AF F) σ y) = sigR (Fv F v) σ (compFin F E v y) := by
        intro y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul a x => rfl
        | add x y hx hy => simp only [map_add, hx, hy]
      rw [hs, splitProj_comp]
    have ha : piW τ (algebraMap (AF F) (AE F E) (Algebra.norm (AF F) z)) = evFin F v (Algebra.norm (AF F) z) := by
      change splitProj τ (compFin F E v (Algebra.norm (AF F) z ⊗ₜ[F] 1)) = _
      simp [compFin]
    rw [map_mul, hc, ha] at h3
    exact h3

end GlobalTheory.NormLocSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorRightPartialPureStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_operator_right_partial_pure : ∀ {F : Type} [Field F] [NumberField F] {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁'] (e : ((κ' → AF F) → ℂ) →ₗ[ℂ] (κ₁' → AF F) → ℂ), IsLocOp e → ∃ P : SInf F (κ ⊕ κ') →L[ℂ] SInf F (κ ⊕ κ₁'), ∀ g ∈ SB (κ ⊕ κ' → Af F), ∃ g₁ ∈ SB (κ ⊕ κ₁' → Af F), ∀ f : SInf F (κ ⊕ κ'), partR e (pureA F f g) = pureA F (P f) g₁ := by
  first | exact @GlobalTheory.DblEval.BlockSwap.partR_pureA | exact GlobalTheory.DblEval.BlockSwap.partR_pureA | (intros; apply GlobalTheory.DblEval.BlockSwap.partR_pureA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalProductActsOfAdelicProductActsFirst
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BoxAct

theorem tens_boxFun {F : Type} [Field F] [NumberField F] {R κ κ' : Type} (ev : AF F → R)
    (φ₁ : (κ → R) → ℂ) (φ₂ : (κ' → R) → ℂ) (r₁ : (κ → AF F) → ℂ) (r₂ : (κ' → AF F) → ℂ) :
    tens ev (boxFun φ₁ φ₂) (boxFun r₁ r₂) = boxFun (tens ev φ₁ r₁) (tens ev φ₂ r₂) := by
  funext x
  simp only [tens, boxFun, Function.comp_def]
  ring

theorem boxFun_acts : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ κ' : Type) [Fintype κ] [Fintype κ']
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (Td : ((κ ⊕ κ' → AF F) → ℂ) → (κ ⊕ κ' → AF F) → ℂ),
    (∀ Φ₁ ∈ schA F κ, ∀ Φ₂ ∈ schA F κ', Td (boxFun Φ₁ Φ₂) = boxFun (T Φ₁) Φ₂) →
    ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ' → Fv F v), ∀ (φ₁' : (κ → Fv F v) → ℂ) (Φ' : (κ ⊕ κ' → Fv F v) → ℂ),
      Acts (evFin F v) T φ₁ φ₁' → Acts (evFin F v) Td (boxFun φ₁ φ₂) Φ' → Φ' = boxFun φ₁' φ₂ := by
  intro F _ _ v κ κ' _ _ T Td hT φ₁ hφ₁ φ₂ hφ₂ φ₁' Φ' h₁ hd
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  obtain ⟨R', hR0', hR'⟩ := GlobalTheory.RestWitness.exists_rest κ' v
  have r₁ := hR φ₁ hφ₁
  have r₂ := hR' φ₂ hφ₂
  have hRest : Rest (evFin F v) (boxFun φ₁ φ₂) (boxFun R R') := by
    refine ⟨fun x z hz => ?_, ?_⟩
    · have hz₁ : At (evFin F v) (z ∘ Sum.inl) := fun u hu => by
        funext i; exact congrFun (hz u hu) (Sum.inl i)
      have hz₂ : At (evFin F v) (z ∘ Sum.inr) := fun u hu => by
        funext i; exact congrFun (hz u hu) (Sum.inr i)
      have e₁ := r₁.1 (x ∘ Sum.inl) (z ∘ Sum.inl) hz₁
      have e₂ := r₂.1 (x ∘ Sum.inr) (z ∘ Sum.inr) hz₂
      simp only [boxFun]
      have a₁ : (x + z) ∘ Sum.inl = x ∘ Sum.inl + z ∘ Sum.inl := rfl
      have a₂ : (x + z) ∘ Sum.inr = x ∘ Sum.inr + z ∘ Sum.inr := rfl
      rw [a₁, a₂, e₁, e₂]
    · rw [tens_boxFun]
      exact GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ' _ r₁.2 _ r₂.2
  have key : tens (evFin F v) Φ' (boxFun R R') = tens (evFin F v) (boxFun φ₁' φ₂) (boxFun R R') := by
    rw [← hd _ hRest, tens_boxFun, hT _ r₁.2 _ r₂.2, h₁ R r₁, tens_boxFun]
  funext y
  let z : κ ⊕ κ' → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
  have hz : ∀ (ι : Type) (w : ι → κ ⊕ κ'), At (evFin F v) (z ∘ w) := by
    intro ι w u hu
    funext i
    exact GlobalTheory.LatVac.at_liftV v (y (w i)) u hu
  have hRz : boxFun R R' z = R 0 * R' 0 := by
    have e₁ := (hR φ₁ hφ₁).1 0 (z ∘ Sum.inl) (hz κ Sum.inl)
    have e₂ := (hR' φ₂ hφ₂).1 0 (z ∘ Sum.inr) (hz κ' Sum.inr)
    rw [zero_add] at e₁ e₂
    simp only [boxFun]
    rw [e₁, e₂]
  have hev : (fun i => evFin F v (z i)) = y := by
    funext i; exact GlobalTheory.LatVac.evFin_liftV v (y i)
  have e := congrFun key z
  simp only [tens, hev, hRz] at e
  exact mul_right_cancel₀ (mul_ne_zero hR0 hR0') e

end GlobalTheory.BoxAct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnipotentRealisedOnAdelicSchwartzStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerUnipotent_realisedOnAdelicSchwartz : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [DecidableEq κ] (C : Matrix κ κ F), Cᵀ = C → Realised ψ (Matrix.fromBlocks 1 0 (-C) 1) := by
  first | exact @GlobalTheory.AdelicSvNQuad.realised_unip | exact GlobalTheory.AdelicSvNQuad.realised_unip | (intros; apply GlobalTheory.AdelicSvNQuad.realised_unip <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfClosedSubmoduleGaussianConvolutionStatement
section
open FourierTransform MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_of_closedSubmodule_gaussian_convolution : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (M : Submodule ℂ (SchwartzMap E ℂ)), IsClosed (M : Set (SchwartzMap E ℂ)) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
    ∀ (b c : ℝ), 0 < b → 0 < c →
    (∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M) →
    ∀ (h u : SchwartzMap E ℂ),
      (∀ y, u y = ∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) →
      u ∈ M := by
  first | exact @GlobalTheory.ConvSeries.mem_of_conv_gaussian | exact GlobalTheory.ConvSeries.mem_of_conv_gaussian | (intros; apply GlobalTheory.ConvSeries.mem_of_conv_gaussian <;> assumption)
end

