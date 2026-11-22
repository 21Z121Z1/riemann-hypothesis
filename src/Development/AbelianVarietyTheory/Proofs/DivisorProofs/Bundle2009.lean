import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1401
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1992
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFirstOfSecond
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0191
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0251
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0246
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0989
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1998
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalWeilHomFinitePlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.LocalWeilHom

theorem tens_cancel {F : Type} [Field F] [NumberField F] (v : Pl F) {κ : Type} [Fintype κ]
    {R : (κ → AF F) → ℂ} (hR : ∀ x z, At (evFin F v) z → R (x + z) = R x) (hR0 : R 0 ≠ 0)
    {φ₁ φ₂ : (κ → Fv F v) → ℂ} (h : tens (evFin F v) φ₁ R = tens (evFin F v) φ₂ R) : φ₁ = φ₂ := by
  funext y
  set z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i) with hz
  have hza : At (evFin F v) z := GlobalTheory.VacAny.at_pi fun i => GlobalTheory.LatVac.at_liftV v _
  have hrx : R (0 + z) = R 0 := hR 0 z hza
  have hy : (fun i => evFin F v ((0 + z) i)) = y := by
    funext i
    simp only [hz, zero_add, GlobalTheory.LatVac.evFin_liftV]
  have e := congrFun h (0 + z)
  simp only [tens] at e
  rw [hrx, hy] at e
  exact mul_right_cancel₀ hR0 e

theorem acts_mul {F : Type} [Field F] [NumberField F] (v : Pl F) {κ : Type} [Fintype κ]
    (T₁ T₂ : Module.End ℂ ((κ → AF F) → ℂ)) (hT₂ : ∀ Φ ∈ schA F κ, T₂ Φ ∈ schA F κ)
    {φ φ' φ'' : (κ → Fv F v) → ℂ} (h₂ : Acts (evFin F v) T₂ φ φ') (h₁ : Acts (evFin F v) T₁ φ' φ'') :
    Acts (evFin F v) (T₁ * T₂) φ φ'' := by
  intro r hr
  have e₂ := h₂ r hr
  have hr' : Rest (evFin F v) φ' r := ⟨hr.1, by rw [← e₂]; exact hT₂ _ hr.2⟩
  show T₁ (T₂ (tens (evFin F v) φ r)) = _
  rw [e₂]
  exact h₁ r hr'

theorem exists_hom {F : Type} [Field F] [NumberField F] (v : Pl F) {κ : Type} [Fintype κ] {Γ : Type} [Monoid Γ]
    (ρ : Γ →* Module.End ℂ ((κ → AF F) → ℂ)) (hpres : ∀ γ, ∀ Φ ∈ schA F κ, ρ γ Φ ∈ schA F κ)
    (hex : ∀ γ, ∀ m ∈ SB (κ → Fv F v), ∃ φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) (ρ γ) m φ₁) :
    ∃ ω : Γ →* Module.End ℂ (SB (κ → Fv F v)), ∀ γ (m : SB (κ → Fv F v)) (φ₁ : (κ → Fv F v) → ℂ),
      φ₁ ∈ SB (κ → Fv F v) → (Acts (evFin F v) (ρ γ) (m : (κ → Fv F v) → ℂ) φ₁ ↔ ((ω γ m : SB (κ → Fv F v)) : (κ → Fv F v) → ℂ) = φ₁) := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (F := F) κ v
  have hRi : ∀ x z, At (evFin F v) z → R (x + z) = R x := (hR 0 (SB _).zero_mem).1
  choose f hfSB hfA using hex

  have hread : ∀ γ (m : (κ → Fv F v) → ℂ) (hm : m ∈ SB (κ → Fv F v)) (φ₁ : (κ → Fv F v) → ℂ),
      Acts (evFin F v) (ρ γ) m φ₁ → ρ γ (tens (evFin F v) m R) = tens (evFin F v) φ₁ R :=
    fun γ m hm φ₁ h => h R (hR m hm)
  have huniq : ∀ γ (m : (κ → Fv F v) → ℂ) (hm : m ∈ SB (κ → Fv F v)) (φ₁ : (κ → Fv F v) → ℂ),
      ρ γ (tens (evFin F v) m R) = tens (evFin F v) φ₁ R → f γ m hm = φ₁ := by
    intro γ m hm φ₁ h
    exact tens_cancel v hRi hR0 ((hread γ m hm _ (hfA γ m hm)).symm.trans h)
  have htadd : ∀ φ φ' : (κ → Fv F v) → ℂ, tens (evFin F v) (φ + φ') R =
      tens (evFin F v) φ R + tens (evFin F v) φ' R := by
    intro φ φ'; funext x; simp only [tens, Pi.add_apply, add_mul]
  have htsmul : ∀ (c : ℂ) (φ : (κ → Fv F v) → ℂ), tens (evFin F v) (c • φ) R = c • tens (evFin F v) φ R := by
    intro c φ; funext x; simp only [tens, Pi.smul_apply, smul_eq_mul, mul_assoc]
  let L : Γ → Module.End ℂ (SB (κ → Fv F v)) := fun γ =>
    { toFun := fun m => ⟨f γ m m.2, hfSB γ m m.2⟩
      map_add' := fun m m' => by
        apply Subtype.ext
        show f γ _ _ = f γ m m.2 + f γ m' m'.2
        apply huniq
        rw [Submodule.coe_add, htadd, map_add, hread γ m m.2 _ (hfA γ m m.2),
          hread γ m' m'.2 _ (hfA γ m' m'.2), htadd]
      map_smul' := fun c m => by
        apply Subtype.ext
        show f γ _ _ = c • f γ m m.2
        apply huniq
        rw [Submodule.coe_smul, htsmul, map_smul, hread γ m m.2 _ (hfA γ m m.2), htsmul] }
  have hL : ∀ γ (m : SB (κ → Fv F v)), ((L γ m : SB (κ → Fv F v)) : (κ → Fv F v) → ℂ) = f γ m m.2 := fun _ _ => rfl
  refine ⟨{ toFun := L, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · apply LinearMap.ext; intro m
    apply Subtype.ext
    rw [hL]
    apply huniq
    rw [map_one]; rfl
  · intro γ γ'
    apply LinearMap.ext; intro m
    apply Subtype.ext
    rw [hL]
    show f (γ * γ') m m.2 = f γ (f γ' m m.2) (hfSB γ' m m.2)
    apply huniq
    rw [map_mul]
    exact acts_mul v (ρ γ) (ρ γ') (hpres γ') (hfA γ' m m.2) (hfA γ _ (hfSB γ' m m.2)) R (hR m m.2)
  · intro γ m φ₁ _
    show _ ↔ f γ m m.2 = φ₁
    constructor
    · intro h; exact huniq γ m m.2 φ₁ (hread γ m m.2 φ₁ h)
    · intro h; rw [← h]; exact hfA γ m m.2

end GlobalTheory.LocalWeilHom

namespace GlobalTheory.LocalWeilHom

theorem local_weil_hom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] (σL : L →+* L) (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L)
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      (∀ g, ιS g ∈ UAt σ G.V' (evFin F v)) → (∀ h, ιT h ∈ UAt σ G.W (evFin F v)) →
    ∃ ω : (Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) × Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →*
        Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v))),
      (∀ g h (m : SB (Fin a' × Fin (a + a') → Fv F v)) (φ₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
        φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v) →
        (Acts (evFin F v) (om' (ιS g, ιT h)) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          ((ω (g, h) m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = φ₁)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w _ _ L _ σL JS JT ιS ιT hιS hιT
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'
  let ρ := om'.comp (MonoidHom.prodMap ιS ιT)
  have hρ : ∀ g h, ρ (g, h) = om' (ιS g, ιT h) := fun _ _ => rfl
  have hpres : ∀ γ, ∀ Φ ∈ schA F (Fin a' × Fin (a + a')), ρ γ Φ ∈ schA F (Fin a' × Fin (a + a')) :=
    fun γ Φ hΦ => hW.pres _ Φ hΦ
  have hex : ∀ γ, ∀ m ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (ρ γ) m φ₁ := by
    rintro ⟨g, h⟩ m hm
    obtain ⟨φ₁, hφ₁, hA₁⟩ := GlobalTheory.T.weilRepresentation_localAtFinitePlace_unitaryGroupW F E σ B a a' G X om om' hTr v (ιT h) (hιT h) m hm
    obtain ⟨S, hS⟩ := GlobalTheory.WeilLocality.locality B G X om om' hTr v (ιS g) (hιS g)
    refine ⟨S φ₁, (hS φ₁ hφ₁).1, ?_⟩
    have hsplit : ρ (g, h) = om' (ιS g, 1) * om' (1, ιT h) := by
      rw [hρ, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    rw [hsplit]
    exact acts_mul v _ _ (fun Φ hΦ => hW.pres _ Φ hΦ) hA₁ (hS φ₁ hφ₁).2
  obtain ⟨ω, hω⟩ := exists_hom v ρ hpres hex
  exact ⟨ω, fun g h m φ₁ hφ₁ => hω (g, h) m φ₁ hφ₁⟩

end GlobalTheory.LocalWeilHom

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalWeilOperatorsSupportedAtPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.LocalWeilOps

theorem comm_off_V {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (Bs : Base F E) (Γ : Geo σ a a') (X : Chars F E) (om : Rep σ Γ.V Γ.W) (om' : Rep σ Γ.V' Γ.W)
    (hTr : IsTriple Bs Γ X om om') (v : Pl F) (x : UA σ Γ.V.J) (hx : x ∈ UAt σ Γ.V (evFin F v)) :
    ∀ u : AF F, evFin F v u = 0 → ∀ p q : Fin a × Fin (a + a') → AF F,
    ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')),
      om (x, 1) (GlobalTheory.WeilM.schr Bs.ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr Bs.ψ (u • p, u • q) (om (x, 1) Φ) := by
  intro u hu p q Φ hΦ
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil
  set w := Γ.M.co.e.symm (p, q) with hw
  have he : Γ.M.co.e (u • w) = (u • p, u • q) := by
    rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
  have h0 : u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x - 1) = 0 := hx u hu
  have hact : GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) ((x, 1) : UA σ Γ.V.J × UA σ Γ.W.J) (u • w) = u • w := by
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x * (u • w) - u • w = (u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x - 1)) * w := by
      rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_smul, smul_sub]
    rw [h0, Matrix.zero_mul, sub_eq_zero] at h1
    simp only [GlobalTheory.WeilM.actAB]
    simpa [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat] using h1
  have h2 := hW.impl (x, 1) (u • w) Φ hΦ
  simp only [GlobalTheory.WeilM.Darboux.rho, he, hact] at h2
  exact h2

theorem locality_V {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (Bs : Base F E) (Γ : Geo σ a a') (X : Chars F E) (om : Rep σ Γ.V Γ.W) (om' : Rep σ Γ.V' Γ.W)
    (hTr : IsTriple Bs Γ X om om') (v : Pl F) (x : UA σ Γ.V.J) (hx : x ∈ UAt σ Γ.V (evFin F v)) :
    ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (x, 1)) φ φ₁ := by
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil
  set T := om (x, 1) with hTdef
  have hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), T Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun Φ hΦ => hW.pres (x, 1) Φ hΦ
  have hcomm := comm_off_V Bs Γ X om om' hTr v x hx
  have hfib := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v Bs.ψ T hTr.base.std (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace Bs.ψ hTr.base.std) hkeep
    (fun μ hμ Φ hΦ => hW.unit μ hμ (x, 1) Φ hΦ) hcomm
  have htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : Fin a × Fin (a + a') → AF F,
      ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p) := by
    intro u hu p Φ hΦ
    have h := hcomm u hu p 0 Φ hΦ
    rw [smul_zero, GlobalTheory.WeilLocality.schr_trans, GlobalTheory.WeilLocality.schr_trans] at h
    exact h
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin a × Fin (a + a')) v
  intro φ hφ
  refine ⟨fun t => (R 0)⁻¹ * T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)), ?_, ?_⟩
  · have h4 := GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ (hkeep _ (hR φ hφ).2)
    exact (GlobalTheory.WeilM.SB _).smul_mem (R 0)⁻¹ h4
  · intro r hr
    funext y
    set u : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hudef
    have hu : evFin F v u = 0 := by simp [hudef, GlobalTheory.LatVac.evFin_liftV]
    set p : Fin a × Fin (a + a') → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) with hpdef
    have hyp : y + u • (-y) = p := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef]
      rw [← GlobalTheory.WeilLocality.liftV_one_mul]
      ring
    have hpat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) p := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    set Φ₀ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R with hΦ₀
    set Φ₁ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r with hΦ₁
    set Φ₂ : (Fin a × Fin (a + a') → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
    have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hR φ hφ).2
    have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ := Submodule.smul_mem _ _ (GlobalTheory.T.adelicSchwartzSpace_translate_mem_of_mem _ _ hm₀)
    have hfz : ∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → (Φ₁ - Φ₂) (y + z) = 0 := by
      intro z hz
      have e1 : r (y + z) = r y := hr.1 y z hz
      have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
      have hpz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (p + z) := fun u' hu' => by
        rw [smul_add, hpat u' hu', hz u' hu', add_zero]
      have e3 : R (p + z) = R 0 := by simpa using (hR φ hφ).1 0 (p + z) hpz
      have e4 : (fun i => evFin F v ((y + z + u • (-y)) i)) = fun i => evFin F v ((y + z) i) := by
        funext i
        simp [hu]
      simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
      rw [e4, e2, e3, e1]
      field_simp
      ring
    have h0 := hfib (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
    have h2 : T Φ₂ y = (r y / R 0) * T Φ₀ p := by
      rw [hΦ₂, map_smul, htr u hu (-y) Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hyp]
    rw [h0, h2]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, hpdef]
    field_simp

theorem read_off {F : Type} [Field F] [NumberField F] {κ : Type} (v : Pl F) (R : (κ → AF F) → ℂ) (hR0 : R 0 ≠ 0)
    (hRi : ∀ x z, At (evFin F v) z → R (x + z) = R x) (φ₁ φ₂ : (κ → Fv F v) → ℂ)
    (h : tens (evFin F v) φ₁ R = tens (evFin F v) φ₂ R) : φ₁ = φ₂ := by
  funext t
  have hz : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i) : κ → AF F) := by
    intro u' hu'
    funext i
    exact GlobalTheory.LatVac.at_liftV v _ u' hu'
  have e := congrFun h (fun i => GlobalTheory.LatVac.liftV v (t i))
  have hR := hRi 0 _ hz
  rw [zero_add] at hR
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hR] at e
  exact mul_right_cancel₀ hR0 e

theorem acts_unique {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl F)
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) {φ : (κ → Fv F v) → ℂ} (hφ : φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v))
    {φ₁ φ₂ : (κ → Fv F v) → ℂ} (h1 : Acts (evFin F v) T φ φ₁) (h2 : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction κ v
  exact read_off v R hR0 (hR φ hφ).1 φ₁ φ₂ ((h1 R (hR φ hφ)).symm.trans (h2 R (hR φ hφ)))

theorem acts_comp {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl F)
    (T₁ T₂ : Module.End ℂ ((κ → AF F) → ℂ)) (hT₁ : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T₁ Φ ∈ GlobalTheory.WeilM.schA F κ)
    {φ φ₁ φ₂ : (κ → Fv F v) → ℂ} (h1 : Acts (evFin F v) T₁ φ φ₁) (h2 : Acts (evFin F v) T₂ φ₁ φ₂) :
    Acts (evFin F v) (T₂ * T₁) φ φ₂ := by
  intro r hr
  have e1 := h1 r hr
  have hr1 : Rest (evFin F v) φ₁ r := ⟨hr.1, e1 ▸ hT₁ _ hr.2⟩
  rw [Module.End.mul_apply, e1, h2 r hr1]

theorem local_ops : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (Γ : Type) [Group Γ] (j : Γ →* UA σ G.V.J × UA σ G.W.J),
      (∀ g, (j g).1 ∈ UAt σ G.V (evFin F v) ∧ (j g).2 ∈ UAt σ G.W (evFin F v)) →
      ∃ ω : Γ →* Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v)), ∀ g (φ : SB (Fin a × Fin (a + a') → Fv F v))
        (φ₁ : (Fin a × Fin (a + a') → Fv F v) → ℂ),
        Acts (evFin F v) (om (j g)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          φ₁ = ((ω g φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v Γ _ j hj
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil
  have hkeep : ∀ g, ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), om g Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun g Φ hΦ => hW.pres g Φ hΦ
  have hsplit : ∀ g, om (j g) = om ((j g).1, 1) * om (1, (j g).2) := by
    intro g
    rw [← map_mul]
    congr 1
    simp [Prod.mk_mul_mk]
  have hex : ∀ g (φ : SB (Fin a × Fin (a + a') → Fv F v)), ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (j g)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) φ₁ := by
    intro g φ
    obtain ⟨φ₁, h₁, a₁⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupW_pairVW F E σ B a a' G X om om' hTr v (j g).2 (hj g).2 φ φ.2
    obtain ⟨φ₂, h₂, a₂⟩ := locality_V B G X om om' hTr v (j g).1 (hj g).1 φ₁ h₁
    refine ⟨φ₂, h₂, ?_⟩
    rw [hsplit g]
    exact acts_comp v _ _ (hkeep _) a₁ a₂
  choose S hS hA using hex
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin a × Fin (a + a')) v
  have hRi := (hR 0 (Submodule.zero_mem _)).1
  have hadd : ∀ g (φ φ' : SB (Fin a × Fin (a + a') → Fv F v)), S g (φ + φ') = S g φ + S g φ' := by
    intro g φ φ'
    apply read_off v R hR0 hRi
    have e1 := hA g (φ + φ') R (hR _ (φ + φ').2)
    have e2 := hA g φ R (hR _ φ.2)
    have e3 := hA g φ' R (hR _ φ'.2)
    have t1 : ∀ ψ₁ ψ₂ : (Fin a × Fin (a + a') → Fv F v) → ℂ,
        tens (evFin F v) (ψ₁ + ψ₂) R = tens (evFin F v) ψ₁ R + tens (evFin F v) ψ₂ R := by
      intro ψ₁ ψ₂; funext x; simp [tens, add_mul]
    rw [← e1, Submodule.coe_add, t1, map_add, e2, e3, ← t1]
  have hsmul : ∀ g (c : ℂ) (φ : SB (Fin a × Fin (a + a') → Fv F v)), S g (c • φ) = c • S g φ := by
    intro g c φ
    apply read_off v R hR0 hRi
    have e1 := hA g (c • φ) R (hR _ (c • φ).2)
    have e2 := hA g φ R (hR _ φ.2)
    have t2 : ∀ ψ : (Fin a × Fin (a + a') → Fv F v) → ℂ,
        tens (evFin F v) (c • ψ) R = c • tens (evFin F v) ψ R := by
      intro ψ; funext x; simp [tens, mul_assoc]
    rw [← e1, Submodule.coe_smul, t2, map_smul, e2, ← t2]
  let ωl : Γ → Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v)) := fun g =>
    { toFun := fun φ => ⟨S g φ, hS g φ⟩
      map_add' := fun φ φ' => Subtype.ext (hadd g φ φ')
      map_smul' := fun c φ => Subtype.ext (hsmul g c φ) }
  have hone : ∀ φ : SB (Fin a × Fin (a + a') → Fv F v), S 1 φ = φ := by
    intro φ
    refine acts_unique v _ φ.2 (hA 1 φ) ?_
    intro r hr
    rw [map_one, map_one]
    rfl
  have hmul : ∀ g h (φ : SB (Fin a × Fin (a + a') → Fv F v)), S (g * h) φ = S g ⟨S h φ, hS h φ⟩ := by
    intro g h φ
    refine acts_unique v _ φ.2 (hA (g * h) φ) ?_
    rw [map_mul, map_mul]
    exact acts_comp v _ _ (hkeep _) (hA h φ) (hA g ⟨S h φ, hS h φ⟩)
  refine ⟨{ toFun := ωl, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · exact LinearMap.ext fun φ => Subtype.ext (hone φ)
  · intro g h
    exact LinearMap.ext fun φ => Subtype.ext (hmul g h φ)
  · intro g φ φ₁
    constructor
    · intro hφ₁
      exact acts_unique v _ φ.2 hφ₁ (hA g φ)
    · rintro rfl
      exact hA g φ

end GlobalTheory.LocalWeilOps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedTupleDataGivenLevelCoeffMaps
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PinnedDataGiven

theorem latEmb_iotaW {D : D7} (T : CoreJ D) (hT : LawsJ T) (i : Fin D.R.m) : LatEmb (Wc D i) (iotaW T i) := by
  have key : ∀ (V : HSp D) (_ : T.V ((i : ℕ) + 1) T.toCore.σ₀ = V) (hr : V.rank = D.R.r),
      LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota ((i : ℕ) + 1)) := by
    rintro V rfl hr
    obtain ⟨_, -, -, -, -, -, -, hemb, -⟩ := hT.adPin _ (inR i) _ T.toCore.good_σ₀
    exact hemb
  exact key _ (hT.spaceW _ (inR i) _ T.toCore.good_σ₀) (rank_Wc i)

set_option maxHeartbeats 2000000 in

theorem exists_pins_given : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) , R.toLevCh.Is A.μ0 → R.grp_chiW → R.IsFam → R.IsModels → R.thP_vP → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → Finite T0 → QGuard R → ∀ i : Fin D.R.m, VStd D i → ∀ (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La), LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev → ∀ (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E) (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W) (c0L : ∀ i : Fin D.R.m, VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).coef.W), Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L → ∃ O' : OMDat T.toCore R i T0 id, D.what₂.embLL.toRatAlgHom.fieldRange ≤ O'.c'.F ∧ O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0) ∧ O'.lev = lev ∧ CoefficientBaseChange R i O'.jL (inC O'.c') (c0L i) O'.c0' := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL hchi hfam hmodels hvP hfw hpb hfin hG i hV lev hlev gramR c0R c0L htie
  obtain ⟨fw⟩ := id hfw
  have hT := fw.laws
  obtain ⟨pd, l₂, c₁, h1, h2, hc⟩ := GlobalTheory.TupleCover.exists_covers T R hT hL hpb hG i (Vc D i).rank
  choose Mφ hMφ hφ using fun t => GlobalTheory.T.exists_level_place_datum_over_number_field D G Pl0 T0 A _ R hL hvP i hV t _ (iotaW T i) (latEmb_iotaW T hT i)
  choose MB hMB hB using fun t => GlobalTheory.T.exists_numberField_heckeCharacter_sqrtNorm_values D G Pl0 T0 A _ R hL i t
  have := c₁.fin
  obtain ⟨c', hc'⟩ := GlobalTheory.TupleCover.exists_coeff_ge T.Q.l (c₁.F ⊔ ⨆ t, (Mφ t ⊔ MB t))
  have h3 : c₁.F ≤ c'.F := le_sup_left.trans hc'
  have h4 : ∀ t, Mφ t ⊔ MB t ≤ c'.F := fun t => ((le_iSup (fun t => Mφ t ⊔ MB t) t).trans le_sup_right).trans hc'
  have hle : T.Q.c.F ≤ c'.F := h1.trans h3
  have hLL := h2.trans h3
  obtain ⟨dδ, U₂, dict₂, xi, -, hcov, hhalf, hxi, hcxi, hmod, -⟩ := hc c' hle h3
  let jL : D.what₂.LL →+* c'.F := D.what₂.embLL.codRestrict c'.F fun x => hLL ⟨x, rfl⟩
  have hjL : (inC c').comp jL = D.what₂.embLL := RingHom.ext fun _ => rfl
  obtain ⟨c0', hc0, hplace⟩ := GlobalTheory.T.exists_coefficientMap_extension_rational_values D G Pl0 T0 A _ R hL hchi hfam hmodels gramR c0R c0L htie i c'.F jL (inC c') hjL
  obtain ⟨Cl, fCl, h, J', bad, Lh, gam, vol, La, Nc, hrep, hbad, hcl⟩ :=
    GlobalTheory.SplitReps.exists_repsR_repsCov R i (hL.βV i) hV c'.F (T.Q.Xo ((i : ℕ) + 1)) c' id dδ
  choose B hBis using fun t => hB t c'.F (le_sup_right.trans (h4 t)) (bad t) (hbad t).2.2.2.2
    fun PP hPP => (hrep t).1.2.1 PP (Or.inr hPP)
  have hodd : Odd ((T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q) := by
    obtain ⟨e1, e2, -⟩ := hT.pins.2.2.2 _ (inR i)
    have h5 := Formalism.L2.NTheta.odd_r D.R
    have h6 := i.2
    have h7 := D.R.m_add_three_le_k
    rw [e1, e2]
    convert h5 using 1
    simp only [Ranks.sigW, Ranks.r]
    omega
  choose epF hepF using fun t => (GlobalTheory.ClassTieCompare.exists_epIs_iff (n := (Vc D i).rank) (Dw := T.Q.Dw ((i : ℕ) + 1))
    (bad t) (B t)).2 fun L cc g d => GlobalTheory.T.law_of_squares_selfDual_splitLattice _ _ _ _ hodd L cc g.1 g.2.2 d.1 d.2
  obtain ⟨io, hw, hio⟩ := GlobalTheory.T.exists_harmonicCoefficientMap_at_weights D T.Q hT.pins κ fw.kap i c'
  choose φ hφis using fun t => hφ t c'.F (le_sup_left.trans (h4 t)) (hhalf t).2.2 (Mfr (dδ t).l₂) fun PP hPP c hc => by
    have hM : (dδ t).l₂.Mb ≤ PP.asIdeal := by
      rw [(hcov t).1.2.2.2.1]
      rcases hPP with hPP | hPP
      · rw [(hhalf t).1]
        exact Ideal.mul_le_left.trans (Ideal.prod_le_inf.trans (Finset.inf_le hPP))
      · exact Ideal.mul_le_right.trans ((hhalf t).2.1 PP hPP)
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ T.Q.H.bar.surjective).1 hc
    refine ⟨b, hM hb, ?_⟩
    change _ = star ((T.Q.H.bar b : 𝓞 D.host.E) : D.host.E)
    rw [T.Q.H.bar_eq]
    exact (star_star _).symm
  choose thAd hth using fun t => GlobalTheory.T.exists_adelicSide_of_models D G Pl0 T0 A _ R hmodels i t _ _ c0' _ (h t) _ (hrep t).1.2.2.1
    (hrep t).1.2.2.2.2.2.1 (v₀ i (sg0 D A))
  have hact := fun c => GlobalTheory.T.levelAction_framedPoints_isAction D G Pl0 T0 A T R hL hT hpb i c lev hlev
  refine ⟨{ c' := c', hle := hle, jL := jL, hV := hT.spaceW _ (inR i) _ rfl, c0' := c0', lev := lev, dδ := dδ, Cl' := Cl,
            bad := bad, Lh := Lh, La := La, Nc := Nc, gam := gam, vol := vol, ep := fun t k => epF t (Lh t k), B := B,
            epF := epF, io := io, hw := hw, φ := φ,
            w := fun t _ q => (dδ t).eF.symm (phiHat (dδ t).c₂ (fun x => (dδ t).eF (φ t x)) q),
            U₂ := U₂, dict₂ := dict₂, xi := xi, thAd := thAd,
            Plc := fun t x => ∃ x₀, Place R i t (h t) c0' (jVx R i t x₀) x }, hLL,
    ⟨⟨hjL, hV, fw.hv₀ i _, ⟨gramR, c0R, c0L, htie, hc0⟩, hlev⟩,
    fun t => ⟨⟨h t, J' t, (hrep t).1, hplace t _ _, hth t, fun _ => Iff.rfl⟩, hBis t, hxi t, hφis t, hhalf t⟩,
    ⟨hact _, hact _⟩,
    hbad, hcl, fun t => ⟨fun _ => rfl, hepF t⟩, hio, fun t k q => AlgEquiv.apply_symm_apply _ _, hcov, hcxi, hmod⟩, rfl, hc0⟩

end GlobalTheory.PinnedDataGiven
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupsSchroedingerFixStandardCharStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_openSubgroups_schroedinger_fix_standardChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (κ : Type) [Fintype κ], ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
      ∃ L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F),
        IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
        IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
        ∀ x ∈ L₁, ∀ y ∈ L₂, GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilCont.adeleJoin D.host.F 0 x, GlobalTheory.WeilCont.adeleJoin D.host.F 0 y) Φ = Φ := by
  first | exact @GlobalTheory.SchrFixNbhd.schr_fix_nbhd | exact GlobalTheory.SchrFixNbhd.schr_fix_nbhd | (intros; apply GlobalTheory.SchrFixNbhd.schr_fix_nbhd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicDualBasisIntegralStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_adelic_dual_basis_integral : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (yy : Fin m → (κ → FiniteAdeleRing (𝓞 F) F)), (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) → (∀ i j, g i (yy j) = if i = j then 1 else 0) →
    ∀ (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ y : (κ → FiniteAdeleRing (𝓞 F) F), ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      ∫⁻ x, ‖(∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2 ≤
        C * GlobalTheory.WeilL2Words.l2A F μ (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) := by
  first | exact @GlobalTheory.WeilL2Words.slice_le_l2A | exact GlobalTheory.WeilL2Words.slice_le_l2A | (intros; apply GlobalTheory.WeilL2Words.slice_le_l2A <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedDictionaryBoundStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framed_dictionary_bound : GlobalTheory.UCls.MassBound → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (x0 : ∀ k, Frame ((U σ).X k).Ψ D.R.r) (FF : ∀ k, Set (ReciprocityTheory.L2DbarEstimates.V (nd ((U σ).X k)))), (∀ k, IsOrth ((U σ).X k) (x0 k) ∧ IsFundSet ((U σ).X k) (x0 k) (FF k)) → ∑ k, muF ((U σ).X k) (x0 k) (FF k) ≤ ENNReal.ofReal (massLev D.host.E D.R.r l.M) := by
  first | exact @GlobalTheory.LevGeo.MassLev.mass_components_le | exact GlobalTheory.LevGeo.MassLev.mass_components_le | (intros; apply GlobalTheory.LevGeo.MassLev.mass_components_le <;> assumption)
end

