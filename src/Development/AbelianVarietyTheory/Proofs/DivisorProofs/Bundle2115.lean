import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1798
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1912
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1928
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2059
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDblLocal
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0364
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPageRunRecord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0571
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0154
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2093

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweDualityForClosure
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal

theorem hTens_transpose {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JB JA xᵀ yᵀ = hTens c JA JB x y := by
  simp only [hTens, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem symp_transpose {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) (ξ : E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    symp c ξ JB JA xᵀ yᵀ = symp c ξ JA JB x y := by
  simp only [symp, hTens_transpose]

def dTr {R E : Type} [CommRing R] [Invertible (2 : R)] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) (ξ : E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) {κ : Type} [Fintype κ]
    (co : Darboux (symp c ξ JA JB) κ) : Darboux (symp c ξ JB JA) κ where
  e := (Matrix.transposeLinearEquiv β α R E).trans co.e
  form w w' := by
    rw [← symp_transpose c ξ JB JA w w', co.form]
    rfl

theorem dTr_e {R E : Type} [CommRing R] [Invertible (2 : R)] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) (ξ : E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) {κ : Type} [Fintype κ]
    (co : Darboux (symp c ξ JA JB) κ) (y : Matrix β α E) : (dTr c ξ JA JB co).e y = co.e yᵀ := rfl

theorem weilX : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
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
      ∃ d' : Darboux (symp (R := Fv F v) (GlobalTheory.HoweLocal.cv σ v) (-1) (GlobalTheory.HoweLocal.Jv v W.J) (GlobalTheory.HoweLocal.Jv v X.J))
        (Fin n × Fin d), (∀ x : Matrix (Fin n) (Fin d) (Fv F v ⊗[F] E), d'.e xᵀ = co.e x) ∧
        IsUWeilB (GlobalTheory.HoweLocal.cv σ v) (sbClass (Fv F v)) (GlobalTheory.LatVac.psiAt ψ v) (-1) (GlobalTheory.HoweLocal.Jv v W.J)
          (GlobalTheory.HoweLocal.Jv v X.J) d' χWv ((om'.comp (eX.symm.toMonoidHom.prodMap eW.symm.toMonoidHom)).comp (MonoidHom.inl _ _)) := by
  intro hP F E _ _ _ _ _ σ hcm n d X W M ψ χX χW om hstd hXh hXd hWh hWd hrX hrW hhX hhW hweil v hv _ om' hom' eX heX eW heW
    co hco χXv χWv hlX hlW
  obtain ⟨-, ⟨dA, hdA, hB⟩, -⟩ := hweil
  refine ⟨dTr _ _ _ _ co, fun x => by rw [dTr_e, Matrix.transpose_transpose], ?_⟩
  have hL : ∀ g, ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ((om'.comp (eX.symm.toMonoidHom.prodMap eW.symm.toMonoidHom)).comp (MonoidHom.inl _ _)) g φ ∈ SB _ ∧
      Acts (evFin F v) ((om.comp (MonoidHom.inl _ _)) (eX.symm g).1) φ
        (((om'.comp (eX.symm.toMonoidHom.prodMap eW.symm.toMonoidHom)).comp (MonoidHom.inl _ _)) g φ) := by
    intro g φ hφ
    have h := hom' (eX.symm g) 1 φ hφ
    simpa using h
  have hc : ∀ y, (dTr _ _ _ _ co).e y = GlobalTheory.LatVac.locCo dA v (y.map (GlobalTheory.HoweLocal.liftE v)) := by
    intro y
    rw [dTr_e, hco]
    have := hdA (yᵀ.map (GlobalTheory.HoweLocal.liftE v))
    simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [← this]
    rfl
  have hS := hB.1
  obtain ⟨dd, omd, h1, h2, h3⟩ := GlobalTheory.HoweLocal.DblLocal.exists_dbl_local F E σ hcm d n W.J X (Fin n × Fin d) dA ψ χW (om.comp (MonoidHom.inl _ _)) hstd hWd hXd
    hrW hhW hB v hv eX heX _ hL _ hc χWv hlW
  exact ⟨⟨⟨fun g φ hφ => (hL g φ hφ).1,
    GlobalTheory.HoweLocal.WeilImpl.impl_local F E σ d n W.J X (Fin n × Fin d) dA ψ (om.comp (MonoidHom.inl _ _)) hstd hS v hv eX heX _ hL _ hc,
    fun _ _ _ => Set.mem_univ _⟩,
    GlobalTheory.HoweLocal.LocUnitNonsplit.isUnitaryOn_local F E σ d n W.J X (Fin n × Fin d) dA ψ (om.comp (MonoidHom.inl _ _)) hstd hS v hv eX heX _ hL _ hc,
    GlobalTheory.HoweLocal.isContOn_locOps_member_nonsplit F E σ d n W.J X (Fin n × Fin d) dA ψ (om.comp (MonoidHom.inl _ _)) hstd hS v hv eX heX _ hL _ hc⟩,
    dd, omd, h1, h2, h3⟩

theorem weilW : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
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
      IsUWeilB (GlobalTheory.HoweLocal.cv σ v) (sbClass (Fv F v)) (GlobalTheory.LatVac.psiAt ψ v) (-1) (GlobalTheory.HoweLocal.Jv v X.J)
        (GlobalTheory.HoweLocal.Jv v W.J) co χXv ((om'.comp (eX.symm.toMonoidHom.prodMap eW.symm.toMonoidHom)).comp (MonoidHom.inr _ _)) := by
  intro hP F E _ _ _ _ _ σ hcm n d X W M ψ χX χW om hstd hXh hXd hWh hWd hrX hrW hhX hhW hweil v hv _ om' hom' eX heX eW heW
    co hco χXv χWv hlX hlW
  obtain ⟨hB, -, -⟩ := hweil
  have hL : ∀ g, ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ((om'.comp (eX.symm.toMonoidHom.prodMap eW.symm.toMonoidHom)).comp (MonoidHom.inr _ _)) g φ ∈ SB _ ∧
      Acts (evFin F v) ((om.comp (MonoidHom.inr _ _)) (eW.symm g).1) φ
        (((om'.comp (eX.symm.toMonoidHom.prodMap eW.symm.toMonoidHom)).comp (MonoidHom.inr _ _)) g φ) := by
    intro g φ hφ
    have h := hom' 1 (eW.symm g) φ hφ
    simpa using h
  have hS := hB.1
  obtain ⟨dd, omd, h1, h2, h3⟩ := GlobalTheory.HoweLocal.DblLocal.exists_dbl_local F E σ hcm n d X.J W (Fin n × Fin d) M.co ψ χX (om.comp (MonoidHom.inr _ _)) hstd
    hXd hWd hrX hhX hB v hv eW heW _ hL _ hco χXv hlX
  exact ⟨⟨⟨fun g φ hφ => (hL g φ hφ).1,
    GlobalTheory.HoweLocal.WeilImpl.impl_local F E σ n d X.J W (Fin n × Fin d) M.co ψ (om.comp (MonoidHom.inr _ _)) hstd hS v hv eW heW _ hL _ hco,
    fun _ _ _ => Set.mem_univ _⟩,
    GlobalTheory.HoweLocal.LocUnitNonsplit.isUnitaryOn_local F E σ n d X.J W (Fin n × Fin d) M.co ψ (om.comp (MonoidHom.inr _ _)) hstd hS v hv eW heW _ hL _ hco,
    GlobalTheory.HoweLocal.isContOn_locOps_member_nonsplit F E σ n d X.J W (Fin n × Fin d) M.co ψ (om.comp (MonoidHom.inr _ _)) hstd hS v hv eW heW _ hL _ hco⟩,
    dd, omd, h1, h2, h3⟩

theorem howeDualityFor_locOps : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.HoweDualityUnitary → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) →
      ∀ om' : UAtGrp σ X (evFin F v) × UAtGrp σ W (evFin F v) →* Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ),
        (∀ g h, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), om' (g, h) φ ∈ SB (Fin n × Fin d → Fv F v) ∧
          Acts (evFin F v) (om (g.1, h.1)) φ (om' (g, h) φ)) → GlobalTheory.Published.HoweDualityFor om' := by
  intro hP hHD F E _ _ _ _ _ σ hCM n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hom v hv om' hom'
  have hinj : Function.Injective (algebraMap F (Fv F v)) := (algebraMap F (Fv F v)).injective
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap hinj
  letI : Invertible (2 : Fv F v) := invertibleOfNonzero two_ne_zero
  letI : Field (Fv F v ⊗[F] E) := (GlobalTheory.HoweLocal.Fld.isField_of_isEmpty F E σ hCM v hv).toField
  obtain ⟨δ, hδ⟩ := GlobalTheory.HoweLocal.quad_exists F E σ hCM v
  obtain ⟨eX, heX⟩ := GlobalTheory.HoweLocal.compIso_exists F E σ hCM n X v
  obtain ⟨eW, heW⟩ := GlobalTheory.HoweLocal.compIso_exists F E σ hCM d W v
  obtain ⟨co, hco⟩ := GlobalTheory.HoweLocal.exists_isLocCo F E σ hCM n d X W M v
  obtain ⟨χXv, hcX, hrXv, hlX⟩ := GlobalTheory.HoweLocal.exists_locChr_of_resEtaPow hP F E σ hCM n χX hhX hrX v hv
  obtain ⟨χWv, hcW, hrWv, hlW⟩ := GlobalTheory.HoweLocal.exists_locChr_of_resEtaPow hP F E σ hCM d χW hhW hrW v hv
  obtain ⟨hψc, hψn, hψ1⟩ := GlobalTheory.HoweLocal.Psi.psiAt_cont_norm_nontriv F ψ hψ v
  have hcv : ∀ x : E, GlobalTheory.HoweLocal.cv σ v (Algebra.TensorProduct.includeRight x) =
      Algebra.TensorProduct.includeRight (σ x) := fun x => by
    simp [GlobalTheory.HoweLocal.cv]
  have hdet : ∀ {m : ℕ} (J : Matrix (Fin m) (Fin m) E), (GlobalTheory.HoweLocal.Jv v J).det =
      Algebra.TensorProduct.includeRight (R := F) (A := Fv F v) J.det := fun J => by
    simp only [GlobalTheory.HoweLocal.Jv]
    exact (AlgHom.map_det _ J).symm
  have hiR : Function.Injective (Algebra.TensorProduct.includeRight (R := F) (A := Fv F v) (B := E)) :=
    Algebra.TensorProduct.includeRight_injective hinj
  have hHX : IsHerm (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v X.J) := by
    refine ⟨fun i j => ?_, ?_⟩
    · simp only [GlobalTheory.HoweLocal.Jv, Matrix.map_apply, hcv, hX]
    · rw [hdet]; exact (isUnit_iff_ne_zero.mpr hXd).map _
  have hWs : ∀ i j, GlobalTheory.HoweLocal.cv σ v ((-1) * GlobalTheory.HoweLocal.Jv v W.J j i) =
      -((-1) * GlobalTheory.HoweLocal.Jv v W.J i j) := fun i j => by
    simp only [GlobalTheory.HoweLocal.Jv, Matrix.map_apply, map_mul, map_neg, map_one, hcv, hW]
    ring
  have hWd' : (GlobalTheory.HoweLocal.Jv v W.J).det ≠ 0 := by
    rw [hdet]; intro h; exact hWd (hiR (h.trans (map_zero _).symm))
  have hWeil : IsUWeilPair (GlobalTheory.HoweLocal.cv σ v) (sbClass (Fv F v)) (GlobalTheory.LatVac.psiAt ψ v) (-1)
      (GlobalTheory.HoweLocal.Jv v X.J) (GlobalTheory.HoweLocal.Jv v W.J) co χXv χWv
      (om'.comp (eX.symm.toMonoidHom.prodMap eW.symm.toMonoidHom)) :=
    ⟨weilW hP F E σ hCM n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hom v hv om' hom' eX heX eW heW co hco
        χXv χWv hlX hlW,
      weilX hP F E σ hCM n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hom v hv om' hom' eX heX eW heW co hco
        χXv χWv hlX hlW,
      GlobalTheory.HoweLocal.isContOn_locOps_nonsplit hP F E σ hCM n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hom v hv om' hom' eX heX eW heW co hco
        χXv χWv hlX hlW⟩
  have hHD' := (hHD (Fv F v) (Fv F v ⊗[F] E) (GlobalTheory.HoweLocal.cv σ v) δ hδ (GlobalTheory.LatVac.psiAt ψ v) hψc hψn hψ1 n d (-1)
    (GlobalTheory.HoweLocal.Jv v X.J) (GlobalTheory.HoweLocal.Jv v W.J) hHX (neg_ne_zero.mpr one_ne_zero) hWs hWd' χXv χWv hcX hcW
    hrXv hrWv (Fin n × Fin d) co _ hWeil).1
  have e : (om'.comp (eX.symm.toMonoidHom.prodMap eW.symm.toMonoidHom)).comp (eX.toMonoidHom.prodMap eW.toMonoidHom) = om' := by
    ext ⟨a, b⟩ : 1
    simp
  have := GlobalTheory.HoweLocal.HoweTransport.howeDualityFor_transport eX eW heX.2.1 heX.2.2 heW.2.1 heW.2.2 _ hHD'
  rwa [e] at this

theorem howeDualityFor_closure : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.HoweDualityUnitary → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) →
      ∀ om' : Subgroup.closure (UAt σ X (evFin F v)) × Subgroup.closure (UAt σ W (evFin F v)) →*
          Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ),
        (∀ g h, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), om' (g, h) φ ∈ SB (Fin n × Fin d → Fv F v) ∧
          Acts (evFin F v) (om (g.1, h.1)) φ (om' (g, h) φ)) → GlobalTheory.Published.HoweDualityFor om' := by
  intro hP hHD F E _ _ _ _ _ σ hCM n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hom v hv
  have key := howeDualityFor_locOps hP hHD F E σ hCM n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hom v hv
  rw [closure_UAt σ X (evFin F v), closure_UAt σ W (evFin F v)]
  exact key

end GlobalTheory.HoweLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexBoundParameterRequirementsEventuallyFamily
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

namespace GlobalTheory.OntoSizeRows

theorem sizeRows_at {D : D7} {L : SizeData₂ D} {Pm : ParameterChoice' D L} (Tp : ParamsT D L Pm) (hK : DV.KapDef D)
    (S : SizesAt L) (hC : Pm.CnW = 10) (hg : ∀ j : Fin 2, ((D.host.g j : ℕ) : ℝ) ≤ Real.exp (9 * L.sc.L))
    (hn : L.sc.x ^ (2 + 8 * L.sc.eps) ≤ D.R.n ∧ (D.R.n : ℝ) ≤ 2 * L.sc.x ^ (2 + 8 * L.sc.eps))
    (hm : Real.sqrt (L.sc.x * L.sc.delta1) ≤ D.R.m)
    (h1 : L.sc.x ^ (L.sc.eps / 4) + L.sc.x ^ (L.sc.eps / 3) + 1 + 3 * Real.log L.sc.x ≤ L.sc.x ^ L.sc.eps / 5)
    (h2 : 11 ≤ L.sc.x ^ (L.sc.ez / 5)) (h6 : 8 * Real.log L.sc.x ^ 2 < L.sc.x ^ 2)
    (h8 : 2 * L.sc.x ^ (L.sc.eps / 5 + L.sc.eps / 100) ≤ Real.sqrt (L.sc.x * L.sc.delta1))
    (h11 : 44 ≤ Real.sqrt (L.sc.x * L.sc.delta1)) : GlobalTheory.IndexAssembly.SizeRows Tp hK := by
  obtain ⟨-, -, -, -, -, -, sQD, -, -, -, -, sDe2, sLw, -⟩ := S
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he := L.sc.eps_pos
  have hel := L.sc.eps_lt
  have hm0 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (show 1 ≤ D.R.m by have := D.R.two_le_m; omega)
  have hn0 : (0 : ℝ) < D.R.n := by have : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _; exact_mod_cast this
  refine ⟨?_, h2, GlobalTheory.T.two_pi_mul_weightLength_le_maxWeightDegree_sq D L Pm Tp hK, by rw [hC], sDe2, ?_, ?_, ?_, GlobalTheory.FinalJoin.RecordRun.k_b'_le Pm
    (GlobalTheory.IndexAssembly.three_le_scale_of_pow_bound h2), ?_, by exact_mod_cast (show (44 : ℝ) ≤ D.R.m by linarith), hn0.le⟩
  ·
    have hlogeta := Pm.logeta
    have heta := L.etaSz_pos
    have a1 : L.etaSz ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4)) := (Real.log_le_iff_le_exp heta).1 hlogeta
    have a2 : (D.R.n : ℝ) ≤ Real.exp (1 + 3 * Real.log L.sc.x) := by
      have e3 : Real.exp (3 * Real.log L.sc.x) = L.sc.x ^ 3 := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hx0]
      rw [Real.exp_add, e3]
      have b1 : L.sc.x ^ (2 + 8 * L.sc.eps) ≤ L.sc.x ^ (3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at b1
      have b2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have b3 : 0 ≤ L.sc.x ^ 3 := by positivity
      nlinarith [hn.2]
    have key : L.etaSz * L.sc.X' * D.R.n ≤ Real.exp (L.sc.L / 5) := by
      have hX : 0 < L.sc.X' := Real.exp_pos _
      calc L.etaSz * L.sc.X' * D.R.n
          ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4)) * L.sc.X' * Real.exp (1 + 3 * Real.log L.sc.x) := by gcongr
        _ = Real.exp (L.sc.x ^ (L.sc.eps / 4) + L.sc.x ^ (L.sc.eps / 3) + (1 + 3 * Real.log L.sc.x)) := by
          unfold Scale.X'; simp only [Real.exp_add]
        _ ≤ Real.exp (L.sc.L / 5) := by
          apply Real.exp_le_exp.2
          unfold Scale.L
          linarith
    have hb45 : L.sc.b ^ ((4 : ℝ) / 5) = Real.exp (L.sc.L * (4 / 5)) := by
      unfold Scale.b; rw [← Real.exp_mul]
    have hX : 0 < L.sc.X' := Real.exp_pos _
    unfold Scale.w'' Scale.b' Scale.a
    rw [hb45, div_div, le_div_iff₀ (by positivity)]
    have e5 : Real.exp (L.sc.L / 5) * Real.exp (L.sc.L * (4 / 5)) = L.sc.b := by
      unfold Scale.b; rw [← Real.exp_add]; ring_nf
    calc L.etaSz * Real.exp (L.sc.L * (4 / 5)) * (L.sc.X' * (L.sc.x * D.R.n))
        = L.sc.x * (L.etaSz * L.sc.X' * D.R.n) * Real.exp (L.sc.L * (4 / 5)) := by ring
      _ ≤ L.sc.x * Real.exp (L.sc.L / 5) * Real.exp (L.sc.L * (4 / 5)) := by gcongr
      _ = L.sc.x * L.sc.b := by rw [mul_assoc, e5]
  · apply GlobalTheory.T.thickSet_density_le_inv_four_Lw
    have a1 : L.sc.x ^ (2 : ℝ) ≤ L.sc.x ^ (2 + 8 * L.sc.eps) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    rw [Real.rpow_two] at a1
    have : ((8 * D.host.Lw : ℕ) : ℝ) < D.R.n := by
      push_cast
      unfold SizeLw at sLw
      linarith
    exact_mod_cast this
  · intro i
    have e : Real.exp (9 * L.sc.L) = L.sc.b ^ 9 := by
      unfold Scale.b; rw [← Real.exp_nat_mul]; norm_num
    rw [← e]; exact hg i
  ·
    have hq : (0 : ℝ) < D.host.q := lt_trans (by positivity) Pm.qd_pow.1
    have hd : (0 : ℝ) < D.host.d := lt_trans (by positivity) Pm.qd_pow.2
    obtain ⟨-, -, q2, -, d2, -⟩ := sQD
    unfold szTh at q2 d2
    push_cast
    rw [Real.log_mul hq.ne' hd.ne']
    linarith
  ·
    have hD := Pm.Del_ge.2.2.2
    have hl := Pm.logDel
    have hN0 : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
    have hm10 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := one_le_pow₀ hm0
    have a1 : (D.R.N D.R.m : ℝ) ≤ (D.s.Del : ℝ) := le_trans (le_mul_of_one_le_right hN0 hm10) hD
    have hX : 0 < L.sc.X' := Real.exp_pos _
    rcases le_or_gt (D.s.Del : ℝ) 0 with h0 | h0
    · linarith
    · have a2 : (D.s.Del : ℝ) ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4) / 2) := (Real.log_le_iff_le_exp h0).1 hl
      have a3 : L.sc.x ^ (L.sc.eps / 4) ≤ L.sc.x ^ (L.sc.eps / 3) :=
        Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
      have a4 : 0 ≤ L.sc.x ^ (L.sc.eps / 4) := by positivity
      have a5 : Real.exp (L.sc.x ^ (L.sc.eps / 4) / 2) ≤ L.sc.X' := by
        unfold Scale.X'; exact Real.exp_le_exp.2 (by linarith)
      linarith

theorem sizeRows_along : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ ι : Fm.Ix x,
    GlobalTheory.IndexAssembly.SizeRows (Fm.parT x hx ι) (Fm.ex x hx ι).kap_def := by
  refine ⟨1 / 100, by norm_num, fun eps he hle => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH hc _ => ?_⟩⟩
  have hez : 0 < Fm.ez := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_ez 0 i]
    exact (Fm.L 0 i).sc.ez_pos
  have hev : ∀ᶠ x : ℝ in Filter.atTop, 11 ≤ x ^ (Fm.ez / 5) :=
    (tendsto_rpow_atTop (by positivity : 0 < Fm.ez / 5)).eventually_ge_atTop 11
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 ((GlobalTheory.T.eventually_rpow_log_inequalities eps he (by linarith)).and hev)
  refine ⟨x0, fun x hx hx0' ι => ?_⟩
  have hsx := Fm.L_x x ι hx
  have hse := Fm.L_eps x ι
  obtain ⟨⟨a1, -, a6, a8, a11⟩, a2⟩ := hx0 x hx0'
  obtain ⟨w1, w2, -⟩ := hc.2.1 x hx ι
  have hd : (Fm.L x ι).sc.delta1 = x ^ (-(eps / 8)) := by unfold Scale.delta1; rw [hsx, hse]
  refine sizeRows_at _ _ (Fm.sizes x hx ι) (Fm.fixed.2.2.2.2.2.2.2 x hx ι).1
    ((hc.1.2.2.2.2.2.2.2.2 x hx ι).2.2.1) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hsx, hse]; exact w1
  · rw [hsx]; exact w2.1
  · rw [hsx, hse]; exact a1
  · rw [hsx, Fm.L_ez x ι]; exact a2
  · rw [hsx]; exact a6
  · rw [hd, hsx, hse]; exact a8
  · rw [hd, hsx]; exact a11

end GlobalTheory.OntoSizeRows
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinitePartIdentity
section
open Matrix NumberField
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.QuotientNormCoisometry

theorem norm_one_le {k : ℕ} : ‖(1 : Matrix (Fin k) (Fin k) ℂ)‖ ≤ 1 := by
  rw [← diagonal_one, l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => by simp

theorem norm_mul_coisom {m k l : ℕ} (T : Matrix (Fin m) (Fin k) ℂ) (W : Matrix (Fin k) (Fin l) ℂ)
    (hW : W * Wᴴ = 1) : ‖T * W‖ = ‖T‖ := by
  have hWt : ‖Wᴴ‖ ≤ 1 := by
    have h1 : ‖Wᴴ‖ * ‖Wᴴ‖ = ‖W * Wᴴ‖ := by
      rw [← l2_opNorm_conjTranspose_mul_self, conjTranspose_conjTranspose]
    rw [hW] at h1
    nlinarith [norm_nonneg Wᴴ, norm_one_le (k := k)]
  have hW1 : ‖W‖ ≤ 1 := by rwa [l2_opNorm_conjTranspose] at hWt
  apply le_antisymm
  · calc ‖T * W‖ ≤ ‖T‖ * ‖W‖ := l2_opNorm_mul _ _
      _ ≤ ‖T‖ := mul_le_of_le_one_right (norm_nonneg _) hW1
  · calc ‖T‖ = ‖T * W * Wᴴ‖ := by rw [Matrix.mul_assoc, hW, Matrix.mul_one]
      _ ≤ ‖T * W‖ * ‖Wᴴ‖ := l2_opNorm_mul _ _
      _ ≤ ‖T * W‖ := mul_le_of_le_one_right (norm_nonneg _) hWt

theorem inv_met {k : ℕ} (Y : Matrix (Fin k) (Fin k) ℂ) (hY : IsUnit Y.det) :
    ((Y⁻¹)ᴴ * Y⁻¹)⁻¹ = Y * Yᴴ := by
  rw [Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ hY, conjTranspose_nonsing_inv,
    nonsing_inv_nonsing_inv _ (by rw [det_conjTranspose]; exact hY.star)]

theorem norm_quot {n d D : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (P : Matrix (Fin D) (Fin n) ℂ)
    (XQ : Matrix (Fin D) (Fin D) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin d) (Fin d) ℂ)
    (hQ : IsUnit XQ.det ∧ (XQ⁻¹)ᴴ * XQ⁻¹ = (P * A⁻¹ * Pᴴ)⁻¹) (hX : IsUnit X.det ∧ (X⁻¹)ᴴ * X⁻¹ = A)
    (V : Matrix (Fin d) (Fin D) ℂ) : ‖Y * V * XQ‖ = ‖Y * (V * P) * X‖ := by
  have hA : A⁻¹ = X * Xᴴ := by rw [← hX.2, inv_met X hX.1]
  have hQinv : IsUnit (XQ⁻¹).det := isUnit_nonsing_inv_det XQ hQ.1
  have hBu : IsUnit (P * A⁻¹ * Pᴴ).det := by
    rw [← isUnit_nonsing_inv_det_iff, ← hQ.2, det_mul, det_conjTranspose]
    exact hQinv.star.mul hQinv
  have hB : P * A⁻¹ * Pᴴ = XQ * XQᴴ := by
    rw [← nonsing_inv_nonsing_inv _ hBu, ← hQ.2, inv_met XQ hQ.1]
  have hW : (XQ⁻¹ * P * X) * (XQ⁻¹ * P * X)ᴴ = 1 := by
    rw [conjTranspose_mul, conjTranspose_mul]
    calc XQ⁻¹ * P * X * (Xᴴ * (Pᴴ * (XQ⁻¹)ᴴ)) = XQ⁻¹ * (P * (X * Xᴴ) * Pᴴ) * (XQ⁻¹)ᴴ := by
          simp only [Matrix.mul_assoc]
      _ = XQ⁻¹ * (XQ * XQᴴ) * (XQ⁻¹)ᴴ := by rw [← hA, hB]
      _ = (XQ⁻¹ * XQ) * (XQᴴ * (XQ⁻¹)ᴴ) := by simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [nonsing_inv_mul _ hQ.1, Matrix.one_mul, ← conjTranspose_mul, nonsing_inv_mul _ hQ.1, conjTranspose_one]
  have e : Y * (V * P) * X = (Y * V * XQ) * (XQ⁻¹ * P * X) := by
    calc Y * (V * P) * X = Y * V * (XQ * XQ⁻¹) * P * X := by
          rw [mul_nonsing_inv _ hQ.1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e, norm_mul_coisom _ _ hW]

theorem htMap_quot {K : Type} [Field K] [NumberField K] [StarRing K] {n d D : ℕ} (H : Matrix (Fin n) (Fin n) K)
    (P : Matrix (Fin D) (Fin n) K) (XQ : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (X' : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (hQ : Formalism.DivisionValues.IsQuotMetric P H XQ)
    (hX : ∀ v : InfinitePlace K, IsUnit (X v).det ∧ ((X v)⁻¹)ᴴ * (X v)⁻¹ = H.map v.embedding)
    (vb : Matrix (Fin d) (Fin D) K) :
    Formalism.HN.htMap (Pi.basisFun K (Fin D)) XQ (Pi.basisFun K (Fin d)) X' vb.mulVecLin =
      Formalism.HN.htMap (Pi.basisFun K (Fin n)) X (Pi.basisFun K (Fin d)) X' (vb * P).mulVecLin := by
  unfold Formalism.HN.htMap
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  unfold Formalism.HN.opNormAt
  have hm : ∀ {a b : ℕ} (M : Matrix (Fin b) (Fin a) K),
      LinearMap.toMatrix (Pi.basisFun K (Fin a)) (Pi.basisFun K (Fin b)) M.mulVecLin = M := fun M => by
    ext i j
    simp [LinearMap.toMatrix_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hm, hm]
  have e : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℂ),
      ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖ = ‖M‖ := fun M => (l2_opNorm_def M).symm
  rw [e, e, Matrix.map_mul, norm_quot (H.map v.embedding) (P.map v.embedding) (XQ v) (X v) (X' v)⁻¹ (hQ v) (hX v)]

section Bound

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef.Tree
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem bound_le {p : PtAt ex Csz} {CF C : ℝ} (d : FunIn p CF) (hC0 : 0 ≤ C) (hC : CF ≤ C) :
    (D.R.m : ℝ) * aOne d.G C p.Z.b ≤ d.O.bIPa C p.Z.b := by
  have hS := LeafFixedPointPairing.GlobalTheory.CompanionTheory.LeafFixedPointPlaceNorm.sig_le d ∅ (fun _ => 0) hC
  have hN := GlobalTheory.BigTop.Fun.Model.N_eq d
  unfold FunData.bIPa aOne
  rw [hN]
  show (D.R.m : ℝ) * (C * D.R.f * (GlobalTheory.ChiGrid.bigN D : ℝ) * p.Z.b * Real.log p.Z.b +
      C * D.R.m * (GlobalTheory.ChiGrid.bigN D : ℝ) ^ 2 * sig d.G) ≤
    C * D.R.f * D.R.m * (GlobalTheory.ChiGrid.bigN D : ℝ) * p.Z.b * Real.log p.Z.b +
      C * (D.R.m : ℝ) ^ 2 * (GlobalTheory.ChiGrid.bigN D : ℝ) ^ 2 * (d.data (fun _ => 1) ∅ fun _ => 0).Sig0 C p.Z.b
  have h0 : 0 ≤ C * (D.R.m : ℝ) ^ 2 * (GlobalTheory.ChiGrid.bigN D : ℝ) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hS h0]

end Bound

open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize in

theorem ipa_tie : Bundle → SetAt → InfK → IPa @Comparison₂ := by
  intro hB hS hI
  obtain ⟨CF0, hI⟩ := hI
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨C0, hI⟩ := hI CF hCF
  obtain ⟨e1, he1, hS⟩ := hS
  refine ⟨e1, he1, fun eps h1 h2 => ?_⟩
  obtain ⟨K, hK⟩ := hS eps h1 h2
  refine ⟨K, fun Fm CH hc hL _ => ?_⟩
  obtain ⟨x1, hx1⟩ := hK Fm CH hc hL
  refine ⟨max C0 (max CF 0), fun C hC => ?_⟩
  have hCF' : CF ≤ C := ((le_max_left _ _).trans (le_max_right _ _)).trans hC
  have hC0 : 0 ≤ C := ((le_max_right _ _).trans (le_max_right _ _)).trans hC
  obtain ⟨x0, hx0⟩ := hI eps C (le_of_max_le_left hC)
  refine ⟨max x0 x1, fun x hx hle i p hp d hd vb hvb => ?_⟩
  obtain ⟨-, a, ha⟩ := hd
  have hset := hx1 x hx (le_of_max_le_right hle) i p hp ha.ok.eser
  have key := hx0 _ (Fm.L x i) (Fm.L_eps x i) ((le_of_max_le_left hle).trans (Fm.L_x x i hx).ge) _ _ _ _ _ _ _ hset
    a.ch ha.ok.is a.atScale ha.ok.field
  have hWF := (hB p hp).1
  have hX : ∀ v : NumberField.InfinitePlace (Fm.D x i).what₂.LL,
      IsUnit (Formalism.L2.DIV.frameOf (((Df p).HV p.P.A3.fam3.base3.μ0).map v.embedding)).det ∧
      ((Formalism.L2.DIV.frameOf (((Df p).HV p.P.A3.fam3.base3.μ0).map v.embedding))⁻¹)ᴴ *
        (Formalism.L2.DIV.frameOf (((Df p).HV p.P.A3.fam3.base3.μ0).map v.embedding))⁻¹ =
        ((Df p).HV p.P.A3.fam3.base3.μ0).map v.embedding := fun v =>
    Formalism.L2.DIV.frameOfSpec _ _ (hWF.HV_pos _ v)
  have k3 := key d.X' d.M ha.test _ hX (d.V p.P.A3.fam3.base3.μ0) (fun x' a' => ha.sums _ (Or.inl rfl) x' a')
  rw [htMap_quot _ _ _ _ _ (hWF.XQ_quot _) hX vb, hvb]
  exact k3.trans (bound_le d hC0 hCF')

end GlobalTheory.QuotientNormCoisometry

end
end

