import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1177
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1128
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1276
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1274
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1287
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1275
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0144
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1283
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemLatGHat
section
namespace GlobalTheory.AdMark

open scoped Matrix

theorem exists_lift {R S La U A : Type} [CommRing R] [CommRing S] [AddCommGroup La] [Module R La] [Module.Projective R La]
    [AddCommGroup U] [Module R U] [AddCommGroup A] [Module S A] (φ : R → S) (fv : U →+ A)
    (hfv : ∀ c x, fv (c • x) = φ c • fv x) (K : A →ₗ[S] A) (hKi : Function.Injective K) (H₁ Hk : AddSubgroup A)
    (hsm : ∀ c, ∀ z ∈ Hk, φ c • z ∈ Hk) (L : Submodule R U) (ι : La →ₗ[R] U) (hι : Function.Injective ι) (N : ℕ)
    (hL : ∀ v, v ∈ L ↔ fv v ∈ Hk) (hK : ∀ z, z ∈ Hk ↔ ∃ y ∈ H₁, K y = z)
    (h1 : ∀ v, fv v ∈ H₁ ↔ ∃ a, ι a = v)
    (ap1 : ∀ y ∈ H₁, ∃ a, ∃ w ∈ H₁, y = fv (ι a) + N • w)
    (apk : ∀ z ∈ Hk, ∃ x ∈ L, ∃ w ∈ Hk, z = fv x + N • w)
    (hdiv : ∀ x z, fv x = N • z → ∃ w, fv w = z ∧ x = N • w) :
    ∃ mk : La →ₗ[R] U, (∀ a, mk a ∈ L) ∧ (∀ a, ∃ w ∈ Hk, fv (mk a) - K (fv (ι a)) = N • w) ∧
      (∀ a, (∃ u ∈ L, mk a = N • u) → ∃ b, a = N • b) ∧ ∀ v ∈ L, ∃ a, ∃ u ∈ L, v = mk a + N • u := by
  let P : Submodule R (U × La) :=
    { carrier := {p | p.1 ∈ L ∧ ∃ w ∈ Hk, fv p.1 - K (fv (ι p.2)) = N • w}
      zero_mem' := ⟨L.zero_mem, 0, zero_mem _, by simp⟩
      add_mem' := by
        rintro p q ⟨hp, w, hw, e⟩ ⟨hq, w', hw', e'⟩
        refine ⟨L.add_mem hp hq, w + w', add_mem hw hw', ?_⟩
        rw [smul_add, ← e, ← e']
        simp only [Prod.fst_add, Prod.snd_add, map_add]
        abel
      smul_mem' := by
        rintro c p ⟨hp, w, hw, e⟩
        refine ⟨L.smul_mem c hp, φ c • w, hsm c w hw, ?_⟩
        rw [smul_comm N, ← e]
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul, hfv, smul_sub] }
  have hs : Function.Surjective ((LinearMap.snd R U La) ∘ₗ P.subtype) := by
    intro a
    obtain ⟨x, hx, w, hw, e⟩ := apk _ ((hK _).2 ⟨_, (h1 _).2 ⟨a, rfl⟩, rfl⟩)
    exact ⟨⟨(x, a), hx, -w, neg_mem hw, by rw [e]; simp⟩, rfl⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property _ LinearMap.id hs
  have hs2 : ∀ a, (s a).1.2 = a := fun a => LinearMap.congr_fun hs a
  let mk : La →ₗ[R] U := (LinearMap.fst R U La) ∘ₗ P.subtype ∘ₗ s
  have m1 : ∀ a, mk a ∈ L := fun a => (s a).2.1
  have m2 : ∀ a, ∃ w ∈ Hk, fv (mk a) - K (fv (ι a)) = N • w := fun a => by
    obtain ⟨w, hw, e⟩ := (s a).2.2
    rw [hs2] at e
    exact ⟨w, hw, e⟩
  refine ⟨mk, m1, m2, ?_, ?_⟩
  · rintro a ⟨u, hu, e⟩
    obtain ⟨w, hw, e'⟩ := m2 a
    obtain ⟨y, hy, ey⟩ := (hK _).1 (sub_mem ((hL u).1 hu) hw)
    have : fv (ι a) = N • y := by
      apply hKi
      rw [map_nsmul, ey, smul_sub, ← e', e, map_nsmul]
      abel
    obtain ⟨x, rfl, ex⟩ := hdiv _ _ this
    obtain ⟨b, rfl⟩ := (h1 _).1 hy
    exact ⟨b, hι (by rw [ex, map_nsmul])⟩
  · intro v hv
    obtain ⟨y, hy, ey⟩ := (hK _).1 ((hL v).1 hv)
    obtain ⟨a, w, hw, rfl⟩ := ap1 y hy
    obtain ⟨w', hw', e'⟩ := m2 a
    obtain ⟨u, hu, eu⟩ := hdiv (v - mk a) (K w - w') (by
      rw [map_sub, ← ey, smul_sub, ← e', map_add, map_nsmul]
      abel)
    refine ⟨a, u, (hL u).2 (hu ▸ sub_mem ((hK _).2 ⟨w, hw, rfl⟩) hw'), ?_⟩
    rw [← eu]
    abel

theorem sub_congr {A : Type} [AddCommGroup A] {x y z w w' : A} {M N c : ℕ} (hc : N = M * c) (e : y - z = M • w)
    (e' : x - z = N • w') : x - y = M • (c • w' - w) := by
  rw [smul_sub, ← mul_smul, ← hc, ← e, ← e']
  abel

end GlobalTheory.AdMark

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdMark

theorem latR_rfl {E : Type} [Field E] [NumberField E] {m : ℕ} (L : Submodule (𝓞 E) (Fin m → E)) :
    latR rfl L = L := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem smul_mem_latGHat {D : D7} (W : HSp D) (k : GA D W) (c : 𝓞 D.host.E) :
    ∀ z ∈ latGHat W k, ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) • z ∈ latGHat W k := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨c • a, (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).smul_mem c ha, z, hz, ?_⟩
    funext i
    rw [Pi.smul_apply, smul_eq_mul, ← _root_.mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
    rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem exists_marking : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (l l₂ : Geo.Tor.Level H) (W : HSp D) (r : ℕ) (hr : W.rank = r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)), LatEmb W ι → l.M ∣ l₂.M → l₂.Mb ≤ l.Mb → ∀ k : GA D W, ∃ mk₂ : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), IsMark l₂ (latR hr (latG W k)) mk₂ ∧ MarkAd l₂ W hr ι k mk₂ ∧ ∀ mk, (∀ a, mk a ∈ latR hr (latG W k)) → MarkAd l W hr ι k mk → MarkOver l l₂ (latR hr (latG W k)) mk mk₂ := by
  intro D H Dw l l₂ W r hr ι hι hM hMb k
  subst hr
  rw [latR_rfl]
  haveI := Dw.proj
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  have hM2 : l₂.M ≠ 0 := by have := l₂.three_le; omega
  let fv : (Fin W.rank → D.host.E) →+ (Fin W.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
    AddMonoidHom.mk' (finVec W) (GlobalTheory.AdLat.cap_fv_add D.host.F)
  have ap : ∀ g : GA D W, ∀ z ∈ latGHat W g, ∃ x ∈ latG W g, ∃ w ∈ latGHat W g, z = fv x + l₂.M • w := by
    intro g
    obtain ⟨a1, a2, -, -, a5, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D W g
    rw [a5]
    exact (GlobalTheory.AdLat.hat_rational_points_and_approx _ _ _ _ a1 a2).2.1 l₂.M (Nat.pos_of_ne_zero hM2)
  obtain ⟨mk₂, m1, m2, m3, m4⟩ := exists_lift (fun c : 𝓞 D.host.E => (1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) fv
    (fun c x => by
      funext i
      change (1 : Af D.host.F) ⊗ₜ[D.host.F] ((c : D.host.E) * x i) = _ * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i)
      rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one])
    (finHom W k).1.mulVecLin
    (fun x y h => by
      have := congrArg (fun v => ((finHom W k)⁻¹).1 *ᵥ v) h
      simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] using this)
    (latGHat W 1) (latGHat W k) (smul_mem_latGHat W k) (latG W k) ι hι.1 l₂.M
    (GlobalTheory.MarkCoset.latG_spec D W k).1 (GlobalTheory.MarkCoset.latG_spec D W k).2
    (fun v => ((GlobalTheory.MarkCoset.latG_spec D W 1).1 v).symm.trans (by rw [← hι.2]; rfl))
    (fun y hy => by
      obtain ⟨x, hx, h⟩ := ap 1 y hy
      rw [← hι.2] at hx
      obtain ⟨a, rfl⟩ := hx
      exact ⟨a, h⟩)
    (ap k) (GlobalTheory.MarkCoset.finVec_div W l₂.M hM2)
  refine ⟨mk₂, ⟨m1, fun a _ => m3 a, fun v hv => ?_⟩, fun a _ => m2 a, fun mk _ hmk a ha => ?_⟩
  · refine Submodule.smul_induction_on hv (fun m hm v hv => ?_) (fun x y hx hy => ?_)
    · obtain ⟨a, u, hu, rfl⟩ := m4 v hv
      refine ⟨m • a, Submodule.smul_mem_smul hm trivial, m • u, Submodule.smul_mem _ m hu, ?_⟩
      rw [smul_add, map_smul, smul_comm m]
    · obtain ⟨a, ha, u, hu, rfl⟩ := hx
      obtain ⟨a', ha', u', hu', rfl⟩ := hy
      exact ⟨a + a', add_mem ha ha', u + u', add_mem hu hu', by rw [map_add, smul_add]; abel⟩
  · obtain ⟨c, hc⟩ := hM
    obtain ⟨w, hw, e⟩ := hmk a (Submodule.smul_mono_left (Ideal.map_mono hMb) ha)
    obtain ⟨w', hw', e'⟩ := m2 a
    replace e : fv (mk a) - (finHom W k).1.mulVecLin (fv (ι a)) = l.M • w := e
    obtain ⟨u, hu, eu⟩ := GlobalTheory.MarkCoset.finVec_div W l.M hM0 (mk₂ a - mk a) (c • w' - w) (by
      exact (fv.map_sub _ _).trans (sub_congr hc e e'))
    refine ⟨u, ((GlobalTheory.MarkCoset.latG_spec D W k).1 u).2 (hu ▸ sub_mem (nsmul_mem hw' c) hw), ?_⟩
    rw [← eu]
    abel

end GlobalTheory.AdMark
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryFixingPlaneComplementMemClosure
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

namespace GlobalTheory.PlaneSU

theorem plane_closure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ e₁ e₂ : Fin M → E, hE σ J e₁ e₂ = 0 → hE σ J e₁ e₁ ≠ 0 → hE σ J e₂ e₂ ≠ 0 → (∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J e₁ e₁ / hE σ J e₂ e₂)) = 0) → ∀ g ∈ SUAdelic σ J, (∀ v : Fin M → E, hE σ J e₁ v = 0 → hE σ J e₂ v = 0 → Matrix.mulVec ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) (fun i => inclR (AF F) (v i)) = (fun i => inclR (AF F) (v i))) → g ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} := by
  intro F E _ _ _ _ _ σ hCM M J hJ S₁ S₂ ε hε hS e₁ e₂ h12 h11 h22 ⟨t, ht⟩ g hg hfix
  obtain ⟨hσσ, hfixF⟩ := GlobalTheory.CMConjInvol.cm_conj_invol_fixed F E σ hCM
  obtain ⟨hs1, hs2, hBA₀, h1₀, h2₀, hker⟩ := GlobalTheory.T.orthogonalAnisotropicPair_planeMatrices_facts F E σ hσσ M J hJ e₁ e₂ h12 h11 h22
  obtain ⟨f₁, hf₁⟩ := hfixF _ hs1
  obtain ⟨f₂, hf₂⟩ := hfixF _ hs2
  have hf₁0 : f₁ ≠ 0 := by rintro rfl; exact h11 (by rw [← hf₁, map_zero])
  have hf₂0 : f₂ ≠ 0 := by rintro rfl; exact h22 (by rw [← hf₂, map_zero])
  obtain ⟨δ, bs, hδ, hb0, hb1, hbb⟩ := GlobalTheory.QuadNormBase.exists_basis F E σ hCM.2.2.1 hσσ
    (GlobalTheory.HermLineZeros.exists_conj_ne hCM)
  have hδ0 : δ ≠ 0 := by rintro rfl; exact hδ ⟨0, by simp⟩
  have hbq0 : -(f₂ / f₁) ≠ 0 := neg_ne_zero.2 (div_ne_zero hf₂0 hf₁0)

  let ιR : E →+* AF F ⊗[F] E := inclR (F := F) (AF F)
  let ι : AF F →+* AF F ⊗[F] E := algebraMap (AF F) (AF F ⊗[F] E)
  let c : AF F ⊗[F] E →+* AF F ⊗[F] E := sigR (AF F) σ
  let θ : AF F ⊗[F] E := (1 : AF F) ⊗ₜ[F] bs 1
  let A := (planeA e₁ e₂).map ιR
  let B := (planeB σ J e₁ e₂).map ιR
  let H := (planeH σ J e₁ e₂).map ιR
  have hιR : ∀ r : F, ιR (algebraMap F E r) = algebraMap F (AF F ⊗[F] E) r := fun r =>
    (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E).commutes r
  have hιF : ∀ r : F, ι (algebraMap F (AF F) r) = algebraMap F (AF F ⊗[F] E) r := fun r =>
    (IsScalarTower.algebraMap_apply F (AF F) (AF F ⊗[F] E) r).symm
  have hcR : ∀ x : E, c (ιR x) = ιR (σ x) := fun x => by simp [c, ιR, sigR, inclR]
  have hcι : ∀ s : AF F, c (ι s) = ι s := StrongApprox.sigR_algebraMap σ
  have hcc : ∀ x, c (c x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r y => simp [c, sigR, hσσ]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hcT : ∀ {m p : Type} (P : Matrix m p E), Formalism.UG.cT c (P.map ιR) = (Formalism.UG.cT (σ : E →+* E) P).map ιR := by
    intro m p P; ext i j; simp [Formalism.UG.cT, hcR]
  have hBA : B * A = 1 := by
    simp only [B, A]; rw [← Matrix.map_mul, hBA₀, Matrix.map_one _ (map_zero ιR) (map_one ιR)]
  have h1 : Formalism.UG.cT c A * J.map ιR = H * B := by
    simp only [A, B, H]; rw [hcT, ← Matrix.map_mul, h1₀, Matrix.map_mul]
  have h2 : J.map ιR * A = Formalism.UG.cT c B * H := by
    simp only [A, B, H]; rw [hcT, ← Matrix.map_mul, h2₀, Matrix.map_mul]
  have hH : H = Matrix.diagonal ![algebraMap F (AF F ⊗[F] E) f₁, algebraMap F (AF F ⊗[F] E) f₂] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [H, planeH, ← hf₁, ← hf₂, hιR]
  have hJu : IsUnit (J.map ιR).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsUnit.mk0 _ hJ.2).map _
  have hθ : θ * θ = ι (algebraMap F (AF F) δ) := by
    rw [hιF, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hbb]
    exact (hιR δ)
  have hcθ : c θ = -θ := by simp [c, θ, sigR, hb1, TensorProduct.tmul_neg]
  have hbH : ι (algebraMap F (AF F) (-(f₂ / f₁))) * algebraMap F (AF F ⊗[F] E) f₁ =
      -algebraMap F (AF F ⊗[F] E) f₂ := by
    rw [hιF, ← map_mul, ← map_neg]; congr 1; field_simp
  have hιinj : Function.Injective ι :=
    Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective

  set G : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) := ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))
    with hGdef
  have hGu : Formalism.UG.cT c G * J.map ιR * G = J.map ιR := ((show HR (AF F) σ J from g).2)
  have hfixM : G * (1 - A * B) = 1 - A * B :=
    GlobalTheory.T.matrix_fixes_lowRankProjector_of_fixes_rationalKernel F E (AF F) M _ _ hBA₀ G (fun v hv => hfix v ((hker v).1 hv).1 ((hker v).1 hv).2)
  obtain ⟨hGemb, hXu⟩ := GlobalTheory.T.unitary_fixing_kernel_eq_oneAddLowRank_of_unitary _ c hcc M (J.map ιR) hJu A B H hBA h1 h2 G hGu hfixM
  have hdetX : (B * G * A).det = 1 := by
    rw [← det_emb hBA, ← hGemb]; exact StrongApprox.mem_SUAdelic.1 hg
  obtain ⟨x, hxX⟩ := GlobalTheory.T.exists_quaternionMatrix_eq_of_unitary_det_one F E σ δ bs hb0 hb1 hbb f₁ f₂ hf₁0 hf₂0 (AF F) (B * G * A) (hH ▸ hXu) hdetX
  have hx1 : nrm x = 1 := by
    apply hιinj
    rw [map_one, ← det_qm ι θ hθ, hxX, hdetX]
  have hpq : ∃ p q : AF F, ε * (algebraMap F (AF F) (-(f₂ / f₁)) - (p ^ 2 - algebraMap F (AF F) δ * q ^ 2)) = 0 := by
    refine GlobalTheory.T.neg_inv_ratio_isNorm_of_neg_ratio_isNorm F E σ δ bs hb0 hb1 hbb f₁ f₂ hf₁0 hf₂0 (AF F) ε t ?_
    have e : inclR (F := F) (AF F) (hE σ J e₁ e₁ / hE σ J e₂ e₂) = algebraMap F (AF F ⊗[F] E) (f₁ / f₂) := by
      rw [← hf₁, ← hf₂, ← map_div₀]; exact hιR _
    rw [← e]; exact ht
  have hxcl : x ∈ closure (H0 (a := δ) (b := -(f₂ / f₁)) ε) :=
    GlobalTheory.T.strongApproximation_quaternion_normOne_split F δ (-(f₂ / f₁)) hδ0 hbq0 S₁ S₂ ε hε hS hpq x hx1

  have hunit : ∀ y : DA F δ (-(f₂ / f₁)), nrm y = 1 →
      Formalism.UG.cT c (emb A B (qm ι θ y)) * J.map ιR * emb A B (qm ι θ y) = J.map ιR := by
    intro y hy
    refine emb_unitary c hBA h1 h2 ?_
    rw [hH]
    exact qm_unitary ι θ c hcι hcθ hθ hbH hy
  have hdet : ∀ y : DA F δ (-(f₂ / f₁)), nrm y = 1 → (emb A B (qm ι θ y)).det = 1 := by
    intro y hy
    rw [det_emb hBA, det_qm ι θ hθ, hy, map_one]
  let Φ : {y : DA F δ (-(f₂ / f₁)) // nrm y = 1} → HA (AF F) σ J := fun y =>
    (⟨Matrix.GeneralLinearGroup.mk'' (emb A B (qm ι θ y.1)) (by rw [hdet y.1 y.2]; exact isUnit_one),
      hunit y.1 y.2⟩ : HR (AF F) σ J)
  have hΦmat : ∀ y, ((HA.mat (AF F) σ J (Φ y)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) = emb A B (qm ι θ y.1) :=
    fun y => rfl

  have hco : ∀ i, Continuous fun y : DA F δ (-(f₂ / f₁)) => coords y i := fun i =>
    (continuous_apply i).comp continuous_induced_dom
  have hstar : Continuous (star : DA F δ (-(f₂ / f₁)) → DA F δ (-(f₂ / f₁))) := by
    refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
    fin_cases i
    · simpa [coords] using hco 0
    · exact ((hco 1).neg).congr fun y => by simp [coords]
    · exact ((hco 2).neg).congr fun y => by simp [coords]
    · exact ((hco 3).neg).congr fun y => by simp [coords]
  have hE0 := GlobalTheory.T.continuous_oneAddLowRankEmbedding_quaternionMatrix F E δ (-(f₂ / f₁)) M A B θ
  have hnstar : ∀ y : {y : DA F δ (-(f₂ / f₁)) // nrm y = 1}, nrm (star y.1) = 1 := fun y => by
    calc nrm (star y.1) = nrm y.1 := by simp [nrm]
      _ = 1 := y.2
  have hinv : ∀ y, ((Φ y)⁻¹ : HA (AF F) σ J) = Φ ⟨star y.1, hnstar y⟩ := by
    intro y
    refine inv_eq_of_mul_eq_one_right ?_
    apply Subtype.ext; apply Units.ext
    change emb A B (qm ι θ y.1) * emb A B (qm ι θ (star y.1)) = 1
    rw [← emb_mul hBA, ← qm_mul ι θ hθ, mul_star_eq, y.2, map_one, qm_one, emb_one]
  have hΦc : Continuous Φ := by
    have hU : Continuous fun y : {y : DA F δ (-(f₂ / f₁)) // nrm y = 1} => (Φ y : HR (AF F) σ J).1 := by
      refine Units.continuous_iff.2 ⟨hE0.comp continuous_subtype_val, ?_⟩
      have e : (fun y : {y : DA F δ (-(f₂ / f₁)) // nrm y = 1} =>
          ((((Φ y : HR (AF F) σ J).1)⁻¹ : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))) =
          fun y => emb A B (qm ι θ (star y.1)) := by
        funext y
        have := congrArg (fun z : HA (AF F) σ J => (((z : HR (AF F) σ J).1 : GL (Fin M) (AF F ⊗[F] E)) :
          Matrix (Fin M) (Fin M) (AF F ⊗[F] E))) (hinv y)
        exact this
      rw [e]
      exact hE0.comp (hstar.comp continuous_subtype_val)
    exact continuous_induced_rng.2 hU
  have hg_eq : g = Φ ⟨x, hx1⟩ := by
    apply Subtype.ext; apply Units.ext
    change G = emb A B (qm ι θ x)
    rw [hxX]; exact hGemb
  have hH0N : H0 (a := δ) (b := -(f₂ / f₁)) ε ⊆ {y | nrm y = 1} := by
    rintro _ ⟨γ, hγ, h, hh, -, rfl⟩
    simp [nrm_mul, nrm_rat, hγ, hh]
  have hx' : (⟨x, hx1⟩ : {y : DA F δ (-(f₂ / f₁)) // nrm y = 1}) ∈ closure (Subtype.val ⁻¹' H0 ε) := by
    rw [closure_subtype, Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype, Set.inter_eq_left.2 hH0N]
    exact hxcl
  have hsub : Φ '' (Subtype.val ⁻¹' H0 ε) ⊆
      {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} := by
    rintro _ ⟨⟨y, hy1⟩, ⟨γ, hγ, h, hh, hεh, hy⟩, rfl⟩
    have hγ1 : nrm (rat γ) = 1 := by rw [nrm_rat, hγ, map_one]
    refine ⟨Φ ⟨rat γ, hγ1⟩, ?_, Φ ⟨h, hh⟩, ?_, ?_⟩
    · refine ⟨StrongApprox.mem_SUAdelic.2 (hdet _ hγ1), ?_⟩
      show HA.mat (AF F) σ J (Φ ⟨rat γ, hγ1⟩) ∈ HFin (AF F) σ J
      have hbE : algebraMap F E (-(f₂ / f₁)) * hE σ J e₁ e₁ = -hE σ J e₂ e₂ := by
        rw [← hf₁, ← hf₂, ← map_mul, ← map_neg]; congr 1; field_simp
      have hdE : IsUnit (emb (planeA e₁ e₂) (planeB σ J e₁ e₂) (qm (algebraMap F E) (bs 1) γ)).det := by
        rw [det_emb hBA₀, det_qm _ _ hbb, hγ, map_one]; exact isUnit_one
      have huE : Formalism.UG.cT (σ : E →+* E) (emb (planeA e₁ e₂) (planeB σ J e₁ e₂) (qm (algebraMap F E) (bs 1) γ)) * J *
          emb (planeA e₁ e₂) (planeB σ J e₁ e₂) (qm (algebraMap F E) (bs 1) γ) = J :=
        emb_unitary (σ : E →+* E) hBA₀ h1₀ h2₀
          (qm_unitary (algebraMap F E) (bs 1) (σ : E →+* E) (fun s => σ.commutes s) hb1 hbb hbE hγ)
      refine ⟨Matrix.GeneralLinearGroup.mk'' _ hdE, huE, ?_⟩
      apply Units.ext
      change (emb (planeA e₁ e₂) (planeB σ J e₁ e₂) (qm (algebraMap F E) (bs 1) γ)).map ιR = emb A B (qm ι θ (rat γ))
      rw [emb_map]
      congr 1
      have hcomp : ιR.comp (algebraMap F E) = ι.comp (algebraMap F (AF F)) :=
        RingHom.ext fun r => (hιR r).trans (hιF r).symm
      have e1 : (qm (algebraMap F E) (bs 1) γ).map ιR = qm (ιR.comp (algebraMap F E)) (ιR (bs 1)) γ := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [qm]
      rw [e1, hcomp]
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    · refine ⟨StrongApprox.mem_SUAdelic.2 (hdet _ hh), fun i j => ?_⟩
      have hεε : ε * ε = ε := by
        have h1 : fstA F (ε * ε) = fstA F ε := by
          rw [map_mul]
          funext w
          change fstA F ε w * fstA F ε w = fstA F ε w
          by_cases hw : w ∈ S₁
          · rw [hε.1 w hw, one_mul]
          · rw [hε.2.1 w hw, zero_mul]
        have h2 : sndA F (ε * ε) = sndA F ε := by
          rw [map_mul]
          refine RestrictedProduct.ext _ _ fun v => ?_
          change evalV F v (sndA F ε * sndA F ε) = evalV F v (sndA F ε)
          rw [map_mul]
          by_cases hv : v ∈ S₂
          · rw [hε.2.2.1 v hv, one_mul]
          · rw [hε.2.2.2 v hv, zero_mul]
        exact Prod.ext h1 h2
      have e2 : qm ι θ h - 1 = ι ε • qm ι θ (h - 1) := by rw [← qm_smul, hεh, qm_sub, qm_one]
      have e : emb A B (qm ι θ h) - 1 = ι ε • (A * qm ι θ (h - 1) * B) := by
        unfold emb; rw [add_sub_cancel_left, e2, Matrix.mul_smul, Matrix.smul_mul]
      change ι ε * (emb A B (qm ι θ h) - 1) i j = (emb A B (qm ι θ h) - 1) i j
      rw [e, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← map_mul, hεε]
    · apply Subtype.ext; apply Units.ext
      change emb A B (qm ι θ y) = emb A B (qm ι θ (rat γ)) * emb A B (qm ι θ h)
      rw [show y = rat γ * h from hy, qm_mul ι θ hθ, emb_mul hBA]
  rw [hg_eq]
  exact closure_mono hsub (image_closure_subset_closure_image hΦc ⟨_, hx', rfl⟩)

end GlobalTheory.PlaneSU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalOperatorsCommonEigenvalueInertPrimeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalOperators_common_eigenvalue_inertPrime : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → ∀ (j : Fin D.R.m) (t : T) (hV : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV j t).H), GlobalTheory.Hk3.IsOpsV R j t hV → ∀ P, Good R t P → conjPl P = P → ∀ (b : List ℕ → ℂ) (y y' : (R.HV j t).H), (∀ s, Formalism.L2.Col.InertTypeOk (Vc D j).rank s → hV P (Finsupp.single (labIn (Vc D j).rank s) 1) y = b s • y ∧ hV P (Finsupp.single (labIn (Vc D j).rank s) 1) y' = b s • y') → ∀ cV : List ℤ →₀ ℂ, ∃ σ : ℂ, hV P cV y = σ • y ∧ hV P cV y' = σ • y' := by
  first | exact @GlobalTheory.InertEig.veig | exact GlobalTheory.InertEig.veig | (intros; apply GlobalTheory.InertEig.veig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalVectorValueUnitaryRankOneGindikinKarpelStatement
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalVector_value_unitaryRankOne_gindikinKarpelevich : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → Even n →
    ∀ (α : Fin (n / 2) → ℂ) (φ : GU σ n → ℂ), IsSphericalU q α φ → φ 1 = 1 →
    ∀ (y : GU σ n), y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ (u : GU σ n), (∀ i j, ¬ (i = lo k ∧ j = (lo k).rev) →
      ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = (1 : Matrix (Fin n) (Fin n) L) i j) →
    φ (y⁻¹ * u) = if Valued.v (((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev) ≤ 1 then 1
      else α k ^ (-ordL (((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev)) *
        (q : ℂ) ^ (ordL (((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev)) := by
  first | exact @GlobalTheory.GKUnitaryRankOne.value_rankOne | exact GlobalTheory.GKUnitaryRankOne.value_rankOne | (intros; apply GlobalTheory.GKUnitaryRankOne.value_rankOne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareIntegrableSmoothSubmoduleGL
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep.CuspidalL2GL
open scoped InnerProductSpace

namespace GlobalTheory.SqIntGL

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def sqN (φ : Sm E a) : Submodule ℂ (Sm E a) :=
  Submodule.span ℂ {ψ | IsAutForm ψ ∧ IsSqInt ψ.1 ∧ ∀ z ∈ Zalg E a, z φ = 0 → z ψ = 0}

variable (μ : Measure (GA E a)) [μ.IsHaarMeasure]

theorem memL2_iff_std {f : GA E a → ℂ} : MemL2Quotient (latticeGL E a) μ f ↔
    LeftInv (latticeGL E a) f ∧ MemLp f 2 (μ.restrict (stdDom (latticeGL E a))) :=
  memL2_iff_fundamental_domain (isFundamentalDomain_stdDom _ μ)

def squareIntegrableSmoothSubmoduleGL : Submodule ℂ (Sm E a) where
  carrier := {ψ | MemL2Quotient (latticeGL E a) μ ψ.1}
  zero_mem' := (memL2_iff_std μ).2 ⟨fun _ _ _ => rfl, MemLp.zero⟩
  add_mem' {x y} hx hy := by
    rw [Set.mem_setOf_eq, memL2_iff_std] at hx hy ⊢
    exact ⟨fun γ hγ g => by simp [hx.1 γ hγ g, hy.1 γ hγ g], hx.2.add hy.2⟩
  smul_mem' c x hx := by
    rw [Set.mem_setOf_eq, memL2_iff_std] at hx ⊢
    exact ⟨fun γ hγ g => by simp [hx.1 γ hγ g], hx.2.const_smul c⟩

theorem mem_l2Sub {ψ : Sm E a} : ψ ∈ squareIntegrableSmoothSubmoduleGL μ ↔ MemL2Quotient (latticeGL E a) μ ψ.1 := Iff.rfl

def l2Map : Sm E a →ₗ[ℂ] L2 (latticeGL E a) μ :=
  toL2ₗ μ (squareIntegrableSmoothSubmoduleGL μ) (fun _ h => (mem_l2Sub μ).1 h) ∘ₗ
    Submodule.linearProjOfIsCompl (squareIntegrableSmoothSubmoduleGL μ) _ (Classical.choose_spec (Submodule.exists_isCompl (squareIntegrableSmoothSubmoduleGL μ)))

theorem l2Map_apply {ψ : Sm E a} (h : ψ ∈ squareIntegrableSmoothSubmoduleGL μ) : l2Map μ ψ = ((mem_l2Sub μ).1 h).toL2 := by
  unfold l2Map
  rw [LinearMap.comp_apply]
  have e := Submodule.linearProjOfIsCompl_apply_left (Classical.choose_spec (Submodule.exists_isCompl (squareIntegrableSmoothSubmoduleGL μ))) ⟨ψ, h⟩
  erw [e]
  rfl

def l2Form : Sm E a →ₗ⋆[ℂ] Sm E a →ₗ[ℂ] ℂ := ((innerₛₗ ℂ).comp (l2Map μ)).compl₂ (l2Map μ)

theorem l2Form_apply {x y : Sm E a} (hx : x ∈ squareIntegrableSmoothSubmoduleGL μ) (hy : y ∈ squareIntegrableSmoothSubmoduleGL μ) :
    l2Form μ x y = ⟪((mem_l2Sub μ).1 hx).toL2, ((mem_l2Sub μ).1 hy).toL2⟫_ℂ := by
  simp only [l2Form, LinearMap.compl₂_apply, LinearMap.comp_apply, l2Map_apply μ hx, l2Map_apply μ hy]
  rfl

theorem re_l2Form_pos {x : Sm E a} (hx : x ∈ squareIntegrableSmoothSubmoduleGL μ) (hc : Continuous x.1) (h0 : x ≠ 0) : 0 < (l2Form μ x x).re := by
  rw [l2Form_apply μ hx hx]
  have : ((mem_l2Sub μ).1 hx).toL2 ≠ 0 := toL2_ne_zero _ hc fun e => h0 (Subtype.ext e)
  first
    | exact (re_inner_self_pos (𝕜 := ℂ)).2 this
    | exact inner_self_pos.2 this
    | exact (RCLike.inner_self_pos).2 this
    | (rw [inner_self_eq_norm_sq_to_K]; norm_cast; simpa using this)

theorem mem_l2Sub_of_isAutForm {ψ : Sm E a} (h : IsAutForm ψ) (h' : IsSqInt ψ.1) : ψ ∈ squareIntegrableSmoothSubmoduleGL μ :=
  memL2_of_isAutForm h h'

end GlobalTheory.SqIntGL

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableLatticeChainWithLinesMatrixFormStatement
section
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_lattice_chain_with_lines_matrix_form : ∀ (Γ O : Type) [Group Γ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n t R : ℕ) (r : Γ →* GL (Fin n) O) (ψ : Fin t → Γ →* Oˣ) (ϖ : O) (M : Fin (R + 1) → Submodule O (Fin n → O)) (rs : Fin t → Fin R), Irreducible ϖ → (∀ x, x ∈ M 0 ↔ ∃ y : Fin n → O, x = fun a => ϖ * y a) → M (Fin.last R) = ⊤ → Monotone M → (∀ g k x, x ∈ M k → (r g : Matrix (Fin n) (Fin n) O).mulVec x ∈ M k) → (∀ s, ∃ x ∈ M (rs s).succ, x ∉ M (rs s).castSucc ∧ M (rs s).succ = M (rs s).castSucc ⊔ Submodule.span O {x} ∧ ∀ g, (r g : Matrix (Fin n) (Fin n) O).mulVec x - (fun a => ((ψ s g : Oˣ) : O) * x a) ∈ M (rs s).castSucc) → ∃ (x : GalMats Γ O n t R) (dim : Fin (R + 1) → ℕ), x.Chain (residue O) r (fun s => GlobalTheory.TripleGal.rk1 (ψ s)) rs dim ∧ dim 0 = 0 ∧ dim (Fin.last R) = n ∧ ∀ s, dim (rs s).succ = dim (rs s).castSucc + 1 := by
  first | exact @GlobalTheory.WachChain.chain_of_lattices | exact GlobalTheory.WachChain.chain_of_lattices | (intros; apply GlobalTheory.WachChain.chain_of_lattices <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubgroupAverageLinearTranslateConstStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subgroupAverage_linear_translate_const : ∀ (H : Type) [Group H] (u v : H → ℂ) (c : ℂ) (g : H), (rStab u).index ≠ 0 → (rStab v).index ≠ 0 → avg (u + v) = avg u + avg v ∧ avg (c • u) = c * avg u ∧ avg (fun x => u (g * x)) = avg u ∧ avg (fun _ : H => c) = c := by
  first | exact @GlobalTheory.AvgLin.avg_linear_translate_const | exact GlobalTheory.AvgLin.avg_linear_translate_const | (intros; apply GlobalTheory.AvgLin.avg_linear_translate_const <;> assumption)
end

