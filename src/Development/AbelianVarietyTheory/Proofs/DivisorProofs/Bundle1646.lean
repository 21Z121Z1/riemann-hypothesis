import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1619
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsSeriesOfTorsionCharacters
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0062
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0913
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0924
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0912
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0228
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1395
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0280
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1611
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1439
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationDarbouxCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1598

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPairPartnerInverseTransposeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryPair_partner_inverse_transpose : ∀ (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E)
    (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
    ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ∀ (a : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
      (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)),
      ∃ (g : GA D S) (h : GA D T), mt T h = a.1.1 ∧ mt S g = (b⁻¹).1.1ᵀ := by
  first | exact @GlobalTheory.WeilPairPartner.pair_partner | exact GlobalTheory.WeilPairPartner.pair_partner | (intros; apply GlobalTheory.WeilPairPartner.pair_partner <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilCharSurjectiveAndMapRangeAl
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HTLat GlobalTheory.EigenSplit
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLat

open KernelNoTorsion GmPoints

theorem exists_subgroup_hom_of_tv {O : Type} [CommRing O] {G : Over (Spec (CommRingCat.of O))}
    [GrpObj G] [IsCommMonObj G] {p : ℕ} {R : Type} [CommRing R] [Algebra O R] (ψ : Tv G p) :
    ∃ (H : Subgroup (specO O R ⟶ G)) (θ : H →* Rˣ),
      ∀ (n : ℕ) (w : specO O R ⟶ torsion G (p ^ n)),
        ∃ h : w ≫ torsion.ι G (p ^ n) ∈ H, θ ⟨_, h⟩ = unitOf (w ≫ ψ.χ n) := by
  have hl : ∀ {x : specO O R ⟶ G} {n : ℕ} (m : ℕ), x ^ p ^ n = 1 → x ^ p ^ (n + m) = 1 :=
    fun m hn => by rw [pow_add, pow_mul, hn, one_pow]
  let H : Subgroup (specO O R ⟶ G) :=
    { carrier := {x | ∃ n : ℕ, x ^ p ^ n = 1}
      one_mem' := ⟨0, one_pow _⟩
      mul_mem' := by
        rintro x y ⟨n, hn⟩ ⟨m, hm⟩
        exact ⟨n + m, by rw [mul_pow, hl m hn, add_comm, hl n hm, _root_.one_mul]⟩
      inv_mem' := by
        rintro x ⟨n, hn⟩
        exact ⟨n, by rw [inv_pow, hn, inv_one]⟩ }
  let θ : H → Rˣ := fun x => unitOf (torsionLift x.1 x.2.choose_spec ≫ ψ.χ x.2.choose)
  have hθ : ∀ (x : H) (n : ℕ) (w : specO O R ⟶ torsion G (p ^ n)),
      w ≫ torsion.ι G (p ^ n) = x.1 → θ x = unitOf (w ≫ ψ.χ n) := fun x n w hw =>
    congrArg unitOf (CharGerm.comp_χ_eq ψ _ _ (by rw [hw, torsionLift_ι]))
  refine ⟨H, MonoidHom.mk' θ fun x y => ?_, fun n w =>
    ⟨⟨n, by rw [← MonObj.comp_pow, torsionι_pow, MonObj.comp_one]⟩, hθ _ n w rfl⟩⟩
  obtain ⟨n, hn⟩ := x.2
  obtain ⟨m, hm⟩ := y.2
  have hx : x.1 ^ p ^ (n + m) = 1 := hl m hn
  have hy : y.1 ^ p ^ (n + m) = 1 := by rw [add_comm]; exact hl n hm
  have hxy : (x * y).1 ^ p ^ (n + m) = 1 := by rw [Subgroup.coe_mul, mul_pow, hx, hy, _root_.one_mul]
  rw [hθ x _ _ (torsionLift_ι _ hx), hθ y _ _ (torsionLift_ι _ hy),
    hθ (x * y) _ _ (torsionLift_ι _ hxy), ← unitOf_mul]
  congr 1
  exact ψ.isChar _ _ _ _ _ (by rw [torsionLift_ι, torsionLift_ι, torsionLift_ι]; rfl)

theorem weilChar_surjective_and_map_range_al :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), Function.Surjective P.weilChar ∧ (LinearMap.range P.al).map (omega P.Gt).subtype = htSpan P.Gt p := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P
  have hs : Function.Surjective P.weilChar := fun χ => by
    obtain ⟨H, θ, hθ⟩ := exists_subgroup_hom_of_tv (R := O) χ
    obtain ⟨κ, hκ⟩ := TorsionCharacter.exists_extend_character (P.toA.comp H.subtype)
      (P.toA_injective.comp H.subtype_injective)
      ((Units.map (algebraMap O C).toMonoidHom).comp θ)
    obtain ⟨s, hs1, hs2⟩ := ChTor.exists_tate_of_character (ChTor.Pts P.A.A) Cˣ p
      (Fact.out : p.Prime).pos (fun a b => mul_comm a b) (weil P.A)
      (fun k hk => ⟨fun l z s hl hz hs => weil_level hk hl hz hs, weil_perfect hk⟩) κ
      fun z z' _ _ => map_mul κ z z'
    refine ⟨Tate.mk s hs1, (P.existsUnique_isWeilChar _).unique (P.isWeilChar_weilChar _)
      fun n w => ?_⟩
    obtain ⟨h, hw⟩ := hθ n w
    rw [Tate.lev_mk, hs2 n _ (P.toA_pow w), ← hw]
    exact (congrArg Units.val (hκ ⟨_, h⟩)).symm
  refine ⟨hs, le_antisymm P.map_range_al_le ?_⟩
  rw [← map_span_dlogTv]
  refine Submodule.map_mono (Submodule.span_le.2 ?_)
  rintro _ ⟨χ, rfl⟩
  obtain ⟨t, rfl⟩ := hs χ
  exact ⟨1 ⊗ₜ t, by rw [P.al_tmul, one_smul]; rfl⟩

end GlobalTheory.HTLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumCompactVacuumReadsDetCharacter
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.RealCompact

theorem realM_tauE {D : D7} (θ : InfFam D) {m n : ℕ} (w : Mx D m n) (ρ : D.what₂.Tau) :
    realM θ w (tauE D ρ) = compAt θ ρ w := by
  have h : ∃ ρ', tauE D ρ = tauE D ρ' := ⟨ρ, rfl⟩
  rw [realM, dif_pos h, ← GlobalTheory.SmoothForms.RealPts.tauE_injective D h.choose_spec]

theorem mat_frMove {D : D7} (θ : InfFam D) (W : HSp D) (X : Data D.host.E W.rank) (k : GA D W)
    (x : Frame X.Ψ W.rank) (ρ : D.what₂.Tau) (τ : X.Ψ) (h : τ.1 = tauE D ρ) :
    mat (frMove θ W rfl X k x) τ = compAt θ ρ (Formalism.L2.Theta.mt W k) * mat x τ := by
  rw [← realM_tauE, ← h]
  rfl

theorem isONFr_frMove {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) (X : Data D.host.E W.rank)
    (hX : IsMod W rfl X) (k : GA D W) (x : Frame X.Ψ W.rank) (hx : IsONFr X x) :
    IsONFr X (frMove θ W rfl X k x) := by
  intro τ
  obtain ⟨ρ, hρ⟩ := (hX.psi τ.1).1 τ.2
  have hu : (compAt θ ρ (Formalism.L2.Theta.mt W k))ᴴ * gramAt D W ρ * compAt θ ρ (Formalism.L2.Theta.mt W k) = gramAt D W ρ :=
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ W k ρ
  have hG : X.Gm.map τ.1 = -(gramAt D W ρ)ᵀ := by
    rw [hX.model.1, hρ]
    ext a b
    exact map_neg (tauE D ρ) _
  have e : ∀ y : Matrix (Fin W.rank) (Fin W.rank) ℂ, FD.gram τ.1 X.Gm y = -(yᴴ * gramAt D W ρ * y)ᵀ := by
    intro y
    have e0 : FD.gram τ.1 X.Gm y = yᵀ * (X.Gm.map τ.1 * yᴴᵀ) := by
      ext a b
      simp only [FD.gram, hermC, FD.col, of_apply, mul_apply, transpose_apply, map_apply, Finset.mul_sum, mul_assoc,
        conjTranspose_apply, RCLike.star_def]
    rw [e0, hG, transpose_mul, transpose_mul, Matrix.neg_mul, Matrix.mul_neg]
  rw [mat_frMove θ W X k x ρ τ hρ, ← hx τ, e, e, conjTranspose_mul]
  congr 2
  conv_rhs => rw [← hu]
  simp only [Matrix.mul_assoc]

theorem om_compact_reads : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ mu : GA D W → ℂ, Formalism.L2.Pj.MuVal W χV mu → ∀ (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsMod W hr X → IsSympl X bas → ∀ (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → IsInvOf W hr X x s → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), IsThetaFunO ψ V W f → Reads θ V W hr X bas idx f φ x → ∀ k ∈ GinfC W, (∀ τ, s τ * compAt θ τ (Formalism.L2.Theta.mt W k) = compAt θ τ (Formalism.L2.Theta.mt W k) * s τ) → Reads θ V W hr X bas idx (om (1, k) f) (mu k • φ) (frMove θ W hr X k x) := by
  intro D ψ θ V W χV χW om hP mu hmu r g hr X bas idx hX hS x s hx hs f φ hf hR k hk hks
  subst hr
  have hstd := hP.weil.std
  obtain ⟨cW, cV, -⟩ := GlobalTheory.FrameCplx.cplx_of_frame D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS x s
    hx hs
  have hvac := GlobalTheory.AdTh.FockVac.isFockVacAt_of_reads D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS x s
    hx hs f φ hf hR
  choose a ha using hP.expV
  choose b hb using hP.expW
  obtain ⟨n, hn⟩ := hP.even
  choose p hp hd using fun τ => GlobalTheory.VacuumCharacter.detPlus_one (n := 0) (s τ) (cW τ).1
  have hom := GlobalTheory.T.vacuum_character_positive_definite_source D ψ θ V W χV χW om hP.weil hP.inf hP.sigV hP.sigW s cV cW _ _ ha hb
    (fun τ => a τ + n) (fun τ => a τ - n) (fun τ => -(p τ + b τ))
    (fun τ => by rw [hn]; push_cast; ring) (fun τ => by rw [hn]; push_cast; ring)
    (fun τ => by rw [hp]; push_cast; ring) f hf hvac 1 (one_mem _) k hk hks
  have hx' := isONFr_frMove hP.inf W X hX k x hx
  have hs' : IsInvOf W rfl X (frMove θ W rfl X k x) s := fun ρ τ h => by
    have e1 : s ρ * mat x τ = -(mat x τ * sgnM X) := hs ρ τ h
    show s ρ * _ = _
    rw [mat_frMove θ W X k x ρ τ h, ← Matrix.mul_assoc, hks, Matrix.mul_assoc, e1, Matrix.mul_neg, Matrix.mul_assoc]
  have h2 := GlobalTheory.AdTh.reads_two_frames D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS x _ s hx hx' hs hs'
    (fun ρ => compAt θ ρ (Formalism.L2.Theta.mt W k)) (fun ρ τ h => mat_frMove θ W X k x ρ τ h) f φ hR
  obtain ⟨y, hy, hyv⟩ := GlobalTheory.VacuumCharacter.exists_root hP.inf W
    (fun τ => (GlobalTheory.SmoothForms.RealPts.gramAt_unit W τ).ne_zero) k hk
  have hmk : mu k = ∏ τ, (compAt θ τ (Formalism.L2.Theta.mt W k)).det ^ a τ := by rw [hmu.2 k y hy, hyv χV a ha]
  have h3 := fun c : ℂ => (GlobalTheory.AdTh.reads_linear_injective D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS
    _ hx' _ _ _ _ h2 h2).1 c 0
  simp only [zero_smul, add_zero] at h3
  rw [hom]
  convert h3 _ using 1
  rw [smul_smul, hmk, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have d2 := (hd τ 1 _ (hks τ)).2
  have h0 : (compAt θ τ (Formalism.L2.Theta.mt W k)).det ≠ 0 := by
    have := congrArg Matrix.det (GlobalTheory.UnitaryChar.compAt_mt_mul θ W τ k k⁻¹)
    rw [mul_inv_cancel, GlobalTheory.UnitaryChar.compAt_mt_one, det_one, det_mul] at this
    exact left_ne_zero_of_mul_eq_one this.symm
  have hn2 : V.rank / 2 = n := by omega
  rw [d2] at h0
  rw [GlobalTheory.UnitaryChar.compAt_mt_one, det_one, _root_.one_zpow, mul_one, hn2]
  conv_lhs => rw [d2]
  have hA := left_ne_zero_of_mul h0
  have hB := right_ne_zero_of_mul h0
  generalize ((1 / 2 : ℂ) • (1 + s τ) * compAt θ τ (Formalism.L2.Theta.mt W k) + (1 / 2 : ℂ) • (1 - s τ)).det = A at hA ⊢
  generalize ((1 / 2 : ℂ) • (1 - s τ) * compAt θ τ (Formalism.L2.Theta.mt W k) + (1 / 2 : ℂ) • (1 + s τ)).det = B at hB ⊢
  rw [mul_zpow, zpow_add₀ hA, zpow_sub₀ hB, zpow_natCast, zpow_natCast, div_pow]
  have := pow_ne_zero n hA
  have := pow_ne_zero n hB
  field_simp

end GlobalTheory.AdTh.RealCompact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepLatticeStabilizerVacuumEqDetCharSmul
section
noncomputable section

namespace GlobalTheory.VacStab

section General

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

theorem idem_mul_eq {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (ε : AF F)
    (e0 : ∀ w, evInf F w ε = 0) (e2 : ∀ u, u ≠ v → evFin F u ε = 0) {g h : GAd σ J}
    (e : proj σ J v g = proj σ J v h) (i j : Fin n) :
    algebraMap (AF F) (AF F ⊗[F] E) ε * (matHom _ σ J g).1 i j =
      algebraMap (AF F) (AF F ⊗[F] E) ε * (matHom _ σ J h).1 i j := by
  have c0 : ∀ w, compInf F E w (algebraMap (AF F) (AF F ⊗[F] E) ε) = 0 := fun w => by
    change evInf F w ε ⊗ₜ[F] (1 : E) = 0
    rw [e0, TensorProduct.zero_tmul]
  have c2 : ∀ u, u ≠ v → compFin F E u (algebraMap (AF F) (AF F ⊗[F] E) ε) = 0 := fun u hu => by
    change evFin F u ε ⊗ₜ[F] (1 : E) = 0
    rw [e2 u hu, TensorProduct.zero_tmul]
  have e' : compFin F E v ((matHom _ σ J g).1 i j) = compFin F E v ((matHom _ σ J h).1 i j) :=
    congrArg (fun x => (matHom _ σ J x).1 i j) e
  rw [← sub_eq_zero, ← add_eq_right (b := 1)]
  refine Model.adTens_eq_one (fun w => ?_) fun u => ?_
  · rw [map_add, map_sub, map_mul, map_mul, c0, map_one]; simp
  · rw [map_add, map_sub, map_mul, map_mul, map_one]
    by_cases hu : u = v
    · subst hu; rw [e']; simp
    · rw [c2 u hu]; simp

end General

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def locPart (W : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) : GA D W →* GA D W :=
  (GlobalTheory.AdelicU.emb D.sp.cm.sig W.gram v).comp (GlobalTheory.AdelicU.proj D.sp.cm.sig W.gram v)

theorem suppPl_locPart (W : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    (k : GA D W) : GlobalTheory.WeilParts.SuppPl ε W (locPart W v k) :=
  (GlobalTheory.AdelicU.Model.suppF_iff W hε _).2 ⟨_, rfl⟩

theorem mt_locPart (W : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    (k : GA D W) : Formalism.L2.Theta.mt W (locPart W v k) =
      algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.mt W k + (1 - algebraMap (AF D.host.F) (AE D) ε • 1) := by
  have h1 := suppPl_locPart W hε k
  obtain ⟨α, rfl, -, h2⟩ := hε
  ext i j
  have h3 : _ * Formalism.L2.Theta.mt W (locPart W v k) i j = _ * Formalism.L2.Theta.mt W k i j :=
    idem_mul_eq D.sp.cm.sig W.gram v (pairA D.host.F 0 α) (fun _ => rfl) h2
      (GlobalTheory.AdelicU.proj_emb_self D.sp.cm.sig W.gram v _) i j
  have h4 := h1 i j
  rw [Matrix.sub_apply] at h4
  rw [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  linear_combination h3 - h4

theorem actO_one_left (V W : HSp D) (k : GA D W) (u : WO V W) :
    actO V W 1 k u = HMul.hMul (Formalism.L2.Theta.mt W k) (u : Matrix (Fin W.rank) (Fin V.rank) (AE D)) := by
  unfold actO
  rw [inv_one, show Formalism.L2.Theta.mt V 1 = 1 from rfl, Matrix.mul_one]

theorem actO_actO_inv (V W : HSp D) (k : GA D W) (u : WO V W) : actO V W 1 k (actO V W 1 k⁻¹ u) = u := by
  rw [actO_one_left, actO_one_left, ← Matrix.mul_assoc]
  unfold Formalism.L2.Theta.mt
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mul]

theorem actO_locPart_mem (V W : HSp D) (LV : Set (Fin V.rank → D.host.E)) (LW : Set (Fin W.rank → D.host.E))
    (v : HeightOneSpectrum (𝓞 D.host.F)) {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {k : GA D W} {u : WO V W}
    (hu : u ∈ latO V W LV LW fun _ => True) (hk : actO V W 1 k u ∈ latO V W LV LW fun _ => True) :
    actO V W 1 (locPart W v k) u ∈ latO V W LV LW fun _ => True := by
  have h1 := GlobalTheory.PlaceModel.latO_le_top _ (GlobalTheory.PlaceModel.placeIdem_smul_mem hε hu)
  have h2 := GlobalTheory.PlaceModel.latO_le_top _ (GlobalTheory.PlaceModel.placeIdem_smul_mem hε hk)
  rw [actO_one_left] at h2
  rw [actO_one_left, mt_locPart W hε, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul]
  exact add_mem h2 (sub_mem hu h1)

theorem locPart_stab (V W : HSp D) (LV : Set (Fin V.rank → D.host.E)) (LW : Set (Fin W.rank → D.host.E))
    (v : HeightOneSpectrum (𝓞 D.host.F)) {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {k : GA D W}
    (hk : ∀ u, u ∈ (latO V W LV LW fun _ => True) ↔ actO V W 1 k u ∈ latO V W LV LW fun _ => True) (u : WO V W) :
    u ∈ (latO V W LV LW fun _ => True) ↔ actO V W 1 (locPart W v k) u ∈ latO V W LV LW fun _ => True := by
  refine ⟨fun hu => actO_locPart_mem V W LV LW v hε hu ((hk u).1 hu), fun hu => ?_⟩
  have h := actO_locPart_mem V W LV LW v hε (k := k⁻¹) hu ((hk _).2 (by rwa [actO_actO_inv]))
  have e := actO_actO_inv V W (locPart W v k)⁻¹ u
  rw [inv_inv] at e
  rwa [map_inv, e] at h

theorem om_vacuum_eq_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ mu : GA D W → ℂ, Formalism.L2.Pj.MuVal W χV mu → ∀ (H : Geo.Tor.Host D.host.E) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), V.rank ≠ 0 → IsSelfDualC V ΛV → IsSelfDualC W ΛW → ∀ (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), (∀ τ, IsCartanInv (gramAt D W τ) (s τ)) → ∀ f, IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f → ∀ k ∈ GfC W, (∀ u, u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) ↔ actO V W 1 k u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True)) → om (1, k) f = mu k • f := by
  intro D ψ θ V W χV χW om hP mu hmu H ΛV ΛW hV0 hV hW s hs f hf k hk hlat
  obtain ⟨mu', h1, hmul, hn, -, hc⟩ := GlobalTheory.Member.exists_muVal D W χV hP.weil.hecS fun a =>
    hmu.eq_one_of_fixed _ (congrArg (fun y : D.host.E => (a : AF D.host.F) ⊗ₜ[D.host.F] y) (map_one D.sp.cm.sig))
  obtain rfl : mu = mu' := funext fun g => by
    obtain ⟨x, hx⟩ := hmu.1 g
    rw [hmu.2 g x hx, h1.2 g x hx]
  have h0 : ∀ g, mu g ≠ 0 := fun g h => by simpa [h] using hn g
  have hone : mu 1 = 1 := mul_left_cancel₀ (h0 1) (by rw [← hmul, one_mul, mul_one])
  have hm : ∀ a b : GA D W, om (1, a * b) f = om (1, a) (om (1, b) f) := fun a b => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  have ho : om (1, 1) f = f := by rw [Prod.mk_one_one, map_one, Module.End.one_apply]
  let K : Subgroup (GA D W) :=
    { carrier := {g | om (1, g) f = mu g • f}
      one_mem' := by change om (1, 1) f = mu 1 • f; rw [ho, hone, one_smul]
      mul_mem' := fun {a b} (ha : om (1, a) f = _) (hb : om (1, b) f = _) => by
        change om (1, a * b) f = mu (a * b) • f
        rw [hm, hb, map_smul, ha, smul_smul, hmul, mul_comm]
      inv_mem' := fun {a} (ha : om (1, a) f = _) => by
        change om (1, a⁻¹) f = mu a⁻¹ • f
        have e := hm a⁻¹ a
        rw [inv_mul_cancel, ho, ha, map_smul] at e
        have e1 : mu a⁻¹ * mu a = 1 := by rw [← hmul, inv_mul_cancel, hone]
        conv_rhs => rw [e, smul_smul, e1, one_smul] }
  have hK : IsClosed (K : Set (GA D W)) :=
    isClosed_eq (continuous_pi fun w => (hP.weil.om_cont f hf.2.theta w).comp (Continuous.prodMk_right 1))
      (hc.smul continuous_const)
  refine GlobalTheory.LevelClosure.mem_of_isClosed D.sp.cm.sig W.gram hK hk fun v => ?_
  have hε : IsPlaceIdem D v (pairA D.host.F 0 (GlobalTheory.AdelicU.singleFin v 1)) :=
    ⟨_, rfl, GlobalTheory.AdelicU.evalV_singleFin_self v 1, fun _ hu => GlobalTheory.AdelicU.evalV_singleFin_ne hu 1⟩
  have hst := locPart_stab V W _ _ v hε hlat
  have hsu := suppPl_locPart W hε k
  change om (1, locPart W v k) f = mu (locPart W v k) • f
  by_cases hv : GlobalTheory.WeilParts.NonSplitAt D v (pairA D.host.F 0 (GlobalTheory.AdelicU.singleFin v 1))
  · obtain ⟨a1, a2⟩ := GlobalTheory.T.nonSplitPlace_stabilizer_fixes_latticeVacuum D ψ θ V W χV χW om hP mu hmu H ΛV ΛW hV hW f hf.2.theta hf.2.lat v _ _ hv hsu hst
    rw [a1, a2 hV0, one_smul]
  · obtain ⟨e, he, hee⟩ := not_not.1 (fun h => hv ⟨hε, h⟩)
    exact GlobalTheory.AdTh.om_vacuum_split_stab D ψ θ V W χV χW om hP mu hmu ΛV ΛW hV hW s hs f hf e _ he (fun i j => by rw [hee]; exact hsu i j) hst

end GlobalTheory.VacStab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRealFixesFockMaximalMinors
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormDict

theorem om_real_fock_eq : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
  (∀ τ, HasInfExp D X.χB τ (-((P.n τ : ℚ) + (P.d : ℚ) / 2))) →
  ∀ g ∈ GinfC X.A, ∀ T, X.om (g, 1) (X.fock T) = X.fock T := by
  intro D cc δ t0 Q P X hX hB g hg T
  set G : D.what₂.Tau → Matrix (Fin X.A.rank) (Fin X.A.rank) ℂ := fun τ => compAt X.θ τ (Formalism.L2.Theta.mt X.A g) with hG
  have hmt : ∀ τ, compAt X.θ τ (Formalism.L2.Theta.mt X.B (1 : GA D X.B)) = 1 := fun τ => by
    rw [GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one]
  have hmove := (GlobalTheory.OrientedHeis.om_pureTensorO D X.ψ X.θ X.A X.B X.χA X.χB X.om hX.2.weil hX.2.inf
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun τ => 1 * G τ) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1 * 1) g 1
    (fun τ => by simp) (fun τ => by simp) (fun τ => by simp [hG]) (fun τ => by rw [hmt])
    X.vac hX.2.vac_theta (MvPolynomial.rename X.var (minorPol D T))).2
  have hsub := GlobalTheory.FockBaseChange.pureTensorO_subst D X.ψ X.θ X.A X.B hX.2.weil.std hX.2.inf (fun _ => 1) G
    (fun _ => 1) (fun _ => 1) X.vac hX.2.vac_theta (MvPolynomial.rename X.var (minorPol D T))
  have hdet : ∀ τ, (compAt X.θ τ (Formalism.L2.Theta.mt X.A g)).det * ((G τ)⁻¹).det = 1 := fun τ => by
    have e := GlobalTheory.WeilVacMove.compAt_mt_mul_inv X.θ τ X.A g
    have hu : IsUnit (G τ) := IsUnit.of_mul_eq_one _ e
    rw [← Matrix.det_mul]
    rw [show compAt X.θ τ (Formalism.L2.Theta.mt X.A g) = G τ from rfl,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu), Matrix.det_one]
  change X.om (g, 1) (pureTensorO X.ψ X.θ X.A X.B (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) X.vac
    (MvPolynomial.rename X.var (minorPol D T))) = pureTensorO X.ψ X.θ X.A X.B (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) X.vac
    (MvPolynomial.rename X.var (minorPol D T))
  rw [hmove, GlobalTheory.T.norm_pair_real_points_smul_adelic_vacuum_det_pow P X hX hB g hg, GlobalTheory.FiniteFock.pureTensorO_smul, hsub, GlobalTheory.T.substitution_inverse_transpose_maximalMinorProduct P X T G, map_smul, smul_smul,
    ← Finset.prod_mul_distrib]
  simp only [← mul_pow, hdet, one_pow, Finset.prod_const_one, one_smul]

end GlobalTheory.NormDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationDarbouxCoordinatesStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_darboux_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) (m n : ℕ) (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E) (ξ : AF F ⊗[F] E) (κ : Type) [Fintype κ]
    (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ)
    (om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ)),
    (∀ p w, ∀ φ ∈ schA F κ, om p (co.rho ψ w φ) = co.rho ψ (actAB (cA σ) p w) (om p φ)) →
    ∃ M : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) → ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      (∀ p h, ∀ φ ∈ schA F κ,
        om p (schr ψ (GlobalTheory.WeilL2Words.archPair F (M p h)) φ) = schr ψ (GlobalTheory.WeilL2Words.archPair F h) (om p φ)) ∧
      ∀ h, Continuous fun p => M p h := by
  first | exact @GlobalTheory.ArchTransportDir.archDir_transport | exact GlobalTheory.ArchTransportDir.archDir_transport | (intros; apply GlobalTheory.ArchTransportDir.archDir_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationL2Isometry
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.WeilL2Isometry

open MeasureTheory GlobalTheory.WeilAdm.HaarSplit
open scoped ENNReal Classical

theorem l2A_eq_of_isUnitaryOn : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] {G : Type} [Group G]
    (om : G →* Module.End ℂ ((κ → AF F) → ℂ)), (∀ p, ∀ φ ∈ schA F κ, om p φ ∈ schA F κ) → IsUnitaryOn (adeleClass F) om →
    ∃ μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧
      ∀ p, ∀ Φ ∈ schA F κ, GlobalTheory.WeilL2Words.l2A F μ (om p Φ) = GlobalTheory.WeilL2Words.l2A F μ Φ := by
  intro F _ _ κ _ G _ om hpres hU
  haveI := volume_isAddHaar F κ
  haveI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  letI mY : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  letI mA : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI : SigmaCompactSpace (κ → FiniteAdeleRing (𝓞 F) F) := sigmaCompactSpace_of_locallyCompact_secondCountable
  set ν : Measure (κ → FiniteAdeleRing (𝓞 F) F) := Measure.addHaar with hν
  haveI : SFinite ν := inferInstance
  haveI : MeasurableAdd (κ → mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  haveI : MeasurableAdd (κ → FiniteAdeleRing (𝓞 F) F) := ContinuousAdd.measurableAdd
  haveI hνH : ν.IsAddHaarMeasure := by rw [hν]; infer_instance
  haveI : ((MeasureTheory.MeasureSpace.volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hμH : Measure.IsAddHaarMeasure (((MeasureTheory.MeasureSpace.volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).map (splitE F κ)) :=
    (splitE F κ).isAddHaarMeasure_map _ (continuous_splitE F κ) (continuous_splitE_symm F κ)
  let em : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃ᵐ (κ → AdeleRing (𝓞 F) F) :=
    (Homeomorph.mk (splitE F κ).toEquiv (continuous_splitE F κ) (continuous_splitE_symm F κ)).toMeasurableEquiv
  have hint : ∀ h : (κ → AdeleRing (𝓞 F) F) → ℝ≥0∞,
      ∫⁻ x, h x ∂(((MeasureTheory.MeasureSpace.volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).map (splitE F κ)) = ∫⁻ p, h (splitE F κ p) ∂((MeasureTheory.MeasureSpace.volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν) :=
    fun h => lintegral_map_equiv h em
  have key : ∀ Ψ ∈ GlobalTheory.WeilM.schA F κ,
      GlobalTheory.WeilL2Words.l2A F ν Ψ = ∫⁻ x, ‖Ψ x‖ₑ ^ 2 ∂(((MeasureTheory.MeasureSpace.volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).map (splitE F κ)) := by
    intro Ψ hΨ
    rw [hint]
    have hHm : Measurable fun p => ‖Ψ (splitE F κ p)‖ₑ ^ 2 :=
      (continuous_comp_splitE F κ Ψ hΨ).measurable.enorm.pow_const 2
    rw [lintegral_prod_symm _ hHm.aemeasurable]
    rfl
  refine ⟨ν, hνH, fun p Φ hΦ => ?_⟩
  rw [key _ (hpres p Φ hΦ), key _ hΦ]
  exact hU _ hμH p Φ hΦ

end GlobalTheory.WeilL2Isometry
end

