import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1447
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1457
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1451
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSystemValueEqRootMulThetaConstant
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical

noncomputable section
namespace GlobalTheory.ZH.EvRoot
open GlobalTheory.ThetaCompare

variable {S : Scheme.{0}}

private theorem val_powFrame_divisor {S : Scheme.{0}} (P : PolAV S) {T : Over S} (h : T ⟶ P.A)
    (τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => h.left) (fun _ => 1))) (k : ℤ)
    (y : T.left) (J : (T.left ⟶ P.A.left) → P.L.ι) :
    val (powFrame P.A P.L h τ k) (𝟙 _) y J = val τ (𝟙 _) y J ^ k := by
  unfold powFrame val gm
  split_ifs
  · exact map_zpow _ _ _
  · exact (one_zpow k).symm

private theorem val_rigPow' {S : Scheme.{0}} (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))) (k : ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ S) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι) :
    val (rigPow P.A P.L rig k) r z J = val rig r z J ^ k := by
  unfold rigPow val gm
  split_ifs
  · exact map_zpow _ _ _
  · exact (one_zpow k).symm

open CommPairing in

theorem exists_root_stalk_pull (hG : GlobalFnsSt) (P : PolAV S) {T : Over S} {N M m : ℕ}
    {rig : LB.Gen (P.L.pull (eSec P.A))}
    {α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![(N : ℤ), -1])}
    (hα : α.IsGen)
    (hn : LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A 1).left)
      (LB.mulGen P.L _ _ _ _ (rigT P.A P.L rig T N) (rigT P.A P.L rig T (-1))))
    {h w : T ⟶ P.A} (hw : w = h ^ m) {τ τ'} (hτ : IsTorsFrame P rig M h τ)
    (hτ' : IsTorsFrame P rig M w τ') {th : LB.Sec (LPow P.A P.L 1 T)} {s : LB.Sec (LPow P.A P.L N T)}
    (hs : IsTwistPull P.A P.L (mulT P.A T m) (snd T P.A ^ m) (lift_snd _ _) N 1 α th s) {v v' : Γ(T.left, ⊤)}
    (hv : IsValueAt P.A P.L N s h (powFrame P.A P.L h τ N) v) (hv' : IsValueAt P.A P.L 1 th w τ' v') (y : T.left) :
    ∃ ξ : (T.left.presheaf.stalk y)ˣ, ξ ^ (M ^ 2) = 1 ∧ gs (𝟙 _) y ⊤ v = ξ.val * gs (𝟙 _) y ⊤ v' := by
  have hL : P.L.IsLB := P.isLB
  obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt hL y
  have e1 := sval_twist hs (ptSecT P.A h).left hJ
  rw [pt_mulT, ← hw, sval_valueAt hv hJ, sval_valueAt hv' hJ] at e1
  refine ⟨val α (ptSecT P.A h).left y J * val τ' (𝟙 _) y J * (val (powFrame P.A P.L h τ N) (𝟙 _) y J)⁻¹, ?_, ?_⟩
  · unfold IsTorsFrame at hτ hτ'
    obtain ⟨hhM, -, β, hβ, hnβ, hcβ⟩ := hτ
    obtain ⟨-, -, β', hβ', hnβ', hcβ'⟩ := hτ'
    have eτ : val τ (𝟙 _) y J ^ ((M : ℤ) ^ 2) = val β h.left y J * val rig T.hom y J := by
      rw [← val_powFrame_divisor, val_corr hJ hcβ (𝟙 _), val_mul hJ, val_pull hJ, val_rigT rig 1 hJ, zpow_one,
        Category.id_comp]
    have eτ' : val τ' (𝟙 _) y J ^ ((M : ℤ) ^ 2) = val β' w.left y J * val rig T.hom y J := by
      rw [← val_powFrame_divisor, val_corr hJ hcβ' (𝟙 _), val_mul hJ, val_pull hJ, val_rigT rig 1 hJ, zpow_one,
        Category.id_comp]
    have orbitMap_conj_smul_one : val α (ptSecT P.A 1).left y J = val rig T.hom y J ^ (N : ℤ) * val rig T.hom y J ^ (-1 : ℤ) := by
      have := val_corr hJ hn (𝟙 _)
      rw [val_pull hJ, val_mul hJ, val_rigT rig _ hJ, val_rigT rig _ hJ, Category.id_comp] at this
      exact this
    have eB1 : val β (T.hom ≫ eSec P.A) y J = val rig T.hom y J ^ ((M : ℤ) ^ 2) * (val rig T.hom y J)⁻¹ := by
      have := val_corr hJ hnβ T.hom
      rw [val_pull hJ, val_mul hJ, val_inv, val_rigPow'] at this
      exact this
    have eB1' : val β' (T.hom ≫ eSec P.A) y J = val rig T.hom y J ^ ((M : ℤ) ^ 2) * (val rig T.hom y J)⁻¹ := by
      have := val_corr hJ hnβ' T.hom
      rw [val_pull hJ, val_mul hJ, val_inv, val_rigPow'] at this
      exact this
    have rA := Reg.two (L := P.L) (y := y) (J := J) α hα (snd T P.A) (snd T P.A ^ m) rfl rfl
    have rB := Reg.two (L := P.L) (y := y) (J := J) (LB.pullGen P.L _ _ β (snd T P.A).left)
      (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen P.L _ _ β hβ _) (snd T P.A) (snd T P.A ^ M)
      (by simp)
      (by show (snd T P.A).left ≫ (mulA P.A M).left = (snd T P.A ^ M).left
          rw [← Over.comp_left, GlobalTheory.DivisibleHom.comp_mulA])
    have rB' := Reg.two (L := P.L) (y := y) (J := J) (LB.pullGen P.L _ _ β' (snd T P.A).left)
      (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen P.L _ _ β' hβ' _) (snd T P.A) (snd T P.A ^ M)
      (by simp)
      (by show (snd T P.A).left ≫ (mulA P.A M).left = (snd T P.A ^ M).left
          rw [← Over.comp_left, GlobalTheory.DivisibleHom.comp_mulA])
    have rF := ((rA.pow hJ (M ^ 2)).mul hJ (rB'.pull hJ (snd T P.A ^ m))).mul hJ
      (((rB.pow hJ N).inv).mul hJ ((rA.pull hJ (snd T P.A ^ M)).inv))
    have hmM : (snd T P.A ^ m) ^ M = (snd T P.A ^ M) ^ m := by
      rw [← pow_mul, ← pow_mul, _root_.mul_comm]
    have hF := Reg.const hG P.isAb hL hJ rF (by
      intro U _ hh
      simp only [CartesianMonoidalCategory.lift_snd, GlobalTheory.SymLiftOdd.comp_pow', hmM]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_pow, ofMul_inv, ofMul_one]
      simp only [← natCast_zsmul]
      push_cast
      module) h 1
    simp only [val_pull hJ, ← Over.comp_left, pt_snd, GlobalTheory.SymLiftOdd.comp_pow', one_pow, hhM, ← hw,
      GlobalTheory.UU.one_left] at hF
    rw [val_powFrame_divisor]
    apply Additive.ofMul.injective
    have f1 := congrArg Additive.ofMul hF
    have f2 := congrArg Additive.ofMul eτ
    have f3 := congrArg Additive.ofMul eτ'
    have f4 := congrArg Additive.ofMul orbitMap_conj_smul_one
    have f5 := congrArg Additive.ofMul eB1
    have f6 := congrArg Additive.ofMul eB1'
    simp only [ofMul_mul, ofMul_zpow, ofMul_pow, ofMul_inv, ofMul_one, ← natCast_zsmul] at f1 f2 f3 f4 f5 f6 ⊢
    push_cast at f1 f2 f3 f4 f5 f6 ⊢
    linear_combination (norm := module) f1 + f3 - (N : ℤ) • f2 + ((M : ℤ) ^ 2) • f4 + f6 - (N : ℤ) • f5
  · have e2 : gs (𝟙 _) y ⊤ v = gs (𝟙 _) y ⊤ v * (val (powFrame P.A P.L h τ N) (𝟙 _) y J).val *
        ((val (powFrame P.A P.L h τ N) (𝟙 _) y J)⁻¹ : (T.left.presheaf.stalk y)ˣ).val := by
      rw [_root_.mul_assoc, Units.mul_inv, _root_.mul_one]
    rw [e2, e1]
    simp only [Units.val_mul]
    ring

private theorem real_pt_nsmul {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) :
    ∀ (c : ℕ) (b : S.Gam), ρ.pt (c • b) = ρ.pt b ^ c := by
  have h0 : ρ.pt 0 = 1 := by
    have := ρ.pt_add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.mp this.symm)
  intro c b
  induction c with
  | zero => rw [zero_smul, h0, pow_zero]
  | succ c ih => rw [succ_nsmul, ρ.pt_add, ih, pow_succ]

private theorem exists_injective_stalk_hom_gs_eq {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) :
    ∃ (y : (baseOver (Sp S.R)).left) (φ : S.R →+* (baseOver (Sp S.R)).left.presheaf.stalk y),
      Function.Injective φ ∧ ∀ a : S.R, gs (𝟙 _) y ⊤ (fn a) = φ a := by
  have hI : IsIntegral (baseOver (Sp S.R)).left := by
    first
    | infer_instance
    | (show IsIntegral (Spec (CommRingCat.of S.R)); infer_instance)
  refine ⟨genericPoint _, (((baseOver (Sp S.R)).left.presheaf.germ ⊤ (genericPoint _) trivial).hom).comp
    (Scheme.ΓSpecIso (CommRingCat.of S.R)).inv.hom, ?_, ?_⟩
  · intro a b h
    have h1 := AlgebraicGeometry.germ_injective_of_isIntegral (baseOver (Sp S.R)).left (U := ⊤) (genericPoint _) trivial
    exact (Scheme.ΓSpecIso (CommRingCat.of S.R)).commRingCatIsoToRingEquiv.symm.injective (h1 h)
  · intro a
    unfold gs
    rw [dif_pos (show _ ∈ (⊤ : (baseOver (Sp S.R)).left.Opens) from trivial)]
    rfl

private theorem exists_rootOfUnity_mul_of_pow_eq_pow {K : Type} [Field K] (a b : K) (n : ℕ) (hn : 0 < n) (h : a ^ n = b ^ n) :
    ∃ u : K, u ^ n = 1 ∧ a = u * b := by
  by_cases hb : b = 0
  · subst hb
    rw [zero_pow hn.ne'] at h
    exact ⟨1, one_pow n, by rw [pow_eq_zero_iff hn.ne'] at h; simp [h]⟩
  · refine ⟨a / b, ?_, (div_mul_cancel₀ a hb).symm⟩
    rw [div_pow, h, div_self (pow_ne_zero n hb)]

theorem ev_eq_root_mul_th : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (x : S.Gam) (j : S.J), ∃ (y : S.Gam) (u : Ω) (k : ℕ), 0 < k ∧ u ^ k = 1 ∧ S.ev x j = u * S.th y := by
  intro o Ω _ _ _ _ S ρ x j
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  obtain ⟨a, e, ha⟩ := ρ.orbit j
  have hpt : ∀ (c : ℕ) (b : S.Gam), ρ.pt (c • b) = ρ.pt b ^ c := real_pt_nsmul ρ
  have hpt0 : ρ.pt 0 = 1 := by simpa using hpt 0 0
  have hzero : ∀ b : S.Gam, (S.r * S.N) • b = 0 := by
    intro b; funext i; simp [nsmul_eq_mul]
  have hN : Odd S.N := by rw [ρ.N_eq]; exact (ρ.n_odd.pow).pow
  have hx : ρ.pt (S.r • a) ^ S.N = 1 := by
    rw [← hpt, smul_smul, show S.N * S.r = 1 * (S.r * S.N) by ring, mul_smul, hzero, smul_zero, hpt0]
  have hM : ρ.pt (S.r • a) ^ (S.r * S.N) = 1 := by
    rw [← hpt, smul_smul, show S.r * S.N * S.r = S.r * (S.r * S.N) by ring, mul_smul, hzero, smul_zero, hpt0]
  have hev : ∀ (i : S.J) (b : S.Gam), IsValueAt ρ.P.A ρ.P.L (S.N : ℤ) (ρ.s i) (ρ.pt b)
      (powFrame ρ.P.A ρ.P.L (ρ.pt b) (ρ.fr b) S.N) (fn (⟨S.ev b i, S.ev_mem b i⟩ : S.R)) := by
    intro i b; have := ρ.ev_val i; unfold IsEvT at this; exact this b
  obtain ⟨y, φ, hφi, hφ⟩ := exists_injective_stalk_hom_gs_eq S
  obtain ⟨ξ1, hξ1, H1⟩ := GlobalTheory.ZH.EvCrd.exists_root_stalk hG ρ.P (T := baseOver (Sp S.R)) (N := S.N)
    (M := S.r * S.N) hN (rig := ρ.rig) (x := ρ.pt (S.r • a)) (h := ρ.pt x) (w := ρ.pt (S.r • a + x)) hx hM
    (ρ.pt_add _ _) (θ := ρ.U a) (ρ.U_sym a) (ρ.fr_tors x) (ρ.fr_tors (S.r • a + x)) y
  have E1 := H1 S.J ρ.s (ρ.s ρ.i₀) (fun l => fn (algebraMap o S.R (S.ρ a l ρ.i₀)))
    (fun l => fn (⟨S.ev x l, S.ev_mem x l⟩ : S.R)) (fn (⟨S.ev (S.r • a + x) ρ.i₀, S.ev_mem _ _⟩ : S.R))
    (ρ.U_act a ρ.i₀) (fun l => hev l x) (hev ρ.i₀ _)
  obtain ⟨ξ2, hξ2, H2⟩ := exists_root_stalk_pull hG ρ.P (T := baseOver (Sp S.R)) (N := S.N) (M := S.r * S.N)
    (m := ρ.n ^ ρ.k) (rig := ρ.rig) (α := ρ.α) ρ.α_gen ρ.α_norm (h := ρ.pt (S.r • a + x))
    (w := ρ.pt ((ρ.n ^ ρ.k) • (S.r • a + x))) (hpt _ _) (ρ.fr_tors _) (ρ.fr_tors _) (th := ρ.th₁)
    (s := ρ.s ρ.i₀) ρ.s_zero (hev ρ.i₀ _) (ρ.th_val _) y
  simp only [hφ] at E1 H2
  rw [Finset.sum_eq_single j (fun l _ hl => by rw [ha l, if_neg hl]; simp)
    (fun hj => absurd (Finset.mem_univ j) hj)] at E1
  rw [ha j, if_pos rfl] at E1
  set K := (S.r * S.N) ^ 2 with hK
  have hKpos : 0 < K := by
    have := S.r_pos; have := S.N_ge; positivity
  have hu1 := congrArg Units.val hξ1
  rw [Units.val_pow_eq_pow_val, Units.val_one] at hu1
  have hu2 := congrArg Units.val hξ2
  rw [Units.val_pow_eq_pow_val, Units.val_one] at hu2
  have hR : (algebraMap o S.R (S.ζ ^ e) * ⟨S.ev x j, S.ev_mem x j⟩) ^ K =
      (⟨S.th ((ρ.n ^ ρ.k) • (S.r • a + x)), S.th_mem _⟩ : S.R) ^ K := by
    apply hφi
    rw [map_pow, map_mul, E1, H2, map_pow, mul_pow, mul_pow, hu1, hu2, _root_.one_mul, _root_.one_mul]
  have hz : (algebraMap o Ω S.ζ) ^ K = 1 := by rw [hK, ← map_pow, S.prim.pow_eq_one, map_one]
  have hΩ := congrArg (fun z : S.R => (z : Ω)) hR
  simp only [SubmonoidClass.coe_pow, Subalgebra.coe_mul, Subalgebra.coe_algebraMap] at hΩ
  rw [mul_pow, map_pow, ← pow_mul, _root_.mul_comm e, pow_mul, hz, one_pow, _root_.one_mul] at hΩ
  obtain ⟨u, hu, hux⟩ := exists_rootOfUnity_mul_of_pow_eq_pow _ _ K hKpos hΩ
  exact ⟨_, u, K, hKpos, hu, hux⟩

end GlobalTheory.ZH.EvRoot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementActsOnFrameColumns
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.TorusMat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] [NumberField E] in

theorem prod_tens_ext {A B : Type} [CommRing A] [CommRing B] [Algebra F A] [Algebra F B] {x y : (A × B) ⊗[F] E}
    (h1 : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) x =
      Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) y)
    (h2 : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) x =
      Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) y) : x = y := by
  have hz : ∀ z : (A × B) ⊗[F] E, z = LinearMap.rTensor E (LinearMap.inl F A B)
        (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z) +
      LinearMap.rTensor E (LinearMap.inr F A B)
        (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) := by
    intro z
    induction z with
    | zero => simp
    | tmul x y => simp [← TensorProduct.add_tmul]
    | add x y hx hy =>
      simp only [map_add]
      rw [add_add_add_comm, ← hx, ← hy]
  rw [hz x, hz y, h1, h2]

theorem ae_ext {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {x y : AE F E}
    (hf : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) x =
      Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) y)
    (hi : ∀ (w : InfinitePlace F) (τ : EmbOver E w), piInf τ x = piInf τ y) : x = y := by
  have h1 : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) x =
      Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) y := by
    refine GlobalTheory.AutFunCompare.infTens_ext fun w => ?_
    obtain ⟨τ⟩ := (inferInstance : Nonempty (EmbOver E w))
    apply (infEmb_bijective h τ).1
    have e : ∀ z : AE F E, infEmb τ (Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)
        (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z)) = piInf τ z := fun z => by
      rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]; rfl
    rw [e, e]; exact hi w τ
  exact prod_tens_ext (A := Ainf F) (B := Af F) h1 hf

end GlobalTheory.TorusMat

namespace GlobalTheory.TorusMat

section Helpers

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piInf_inclR {w : InfinitePlace F} (τ : EmbOver E w) (x : E) :
    piInf τ (inclR (F := F) (AF F) x) = τ.1 x := by
  change infEmb τ (evInf F w 1 ⊗ₜ[F] x) = _
  simp

theorem piInf_infScale {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (s : ℝ) :
    piInf τ (algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F s)) = s := by
  have := h.1
  have hr : w.IsReal := IsTotallyReal.isReal w
  change infEmb τ (evInf F w (GlobalTheory.TorusTheta.infScale F s) ⊗ₜ[F] (1 : E)) = _
  rw [infEmb_tmul, map_one, mul_one]
  have e := congrArg (fun p : mixedEmbedding.mixedSpace F => p.1 ⟨w, hr⟩)
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (algebraMap ℝ (mixedEmbedding.mixedSpace F) s))
  simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at e
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hr]
  exact congrArg (fun x : ℝ => (x : ℂ)) (e.trans rfl)

theorem snd_infScale (s : ℝ) :
    Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F s)) = 1 := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
  rfl

end Helpers

theorem isTorusElt_mat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E)
    (t : Fin r₀ → ℝ), (∀ i, 0 < t i) → ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ J Xf Yf t a →
    ((HA.mat (AF F) σ J a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) * incM F Xf =
        incM F Xf * Matrix.diagonal (fun i => algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F (t i))) ∧
      ((HA.mat (AF F) σ J a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) * incM F Yf =
        incM F Yf * Matrix.diagonal (fun i => algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F (t i)⁻¹)) ∧
      ∀ z : Fin n → E, (Formalism.UG.cT (σ : E →+* E) Xf * J) *ᵥ z = 0 → (Formalism.UG.cT (σ : E →+* E) Yf * J) *ᵥ z = 0 →
        ((HA.mat (AF F) σ J a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ
          (fun i => inclR (F := F) (AF F) (z i)) = fun i => inclR (F := F) (AF F) (z i) := by
  intro F E _ _ _ _ _ σ h n J r₀ Xf Yf t _ a ha
  let M : Matrix (Fin n) (Fin n) (AE F E) := ((HA.mat (AF F) σ J a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))
  let ψ : AE F E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
  have f1 : M.map ψ = 1 :=
    congrArg (fun u : GL (Fin n) (Af F ⊗[F] E) => (u : Matrix (Fin n) (Fin n) (Af F ⊗[F] E))) (MonoidHom.mem_ker.1 ha.1)
  have f2 : ∀ s : Fin r₀ → ℝ, (Matrix.diagonal fun i => algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F (s i))).map ψ = 1 :=
    fun s => by
      rw [Matrix.diagonal_map (map_zero _)]
      simp only [ψ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, snd_infScale, Matrix.diagonal_one]
  have g1 : ∀ (w : InfinitePlace F) (τ : EmbOver E w), M.map (piInf τ) = GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) :=
    fun w τ => rfl
  have g2 : ∀ (w : InfinitePlace F) (τ : EmbOver E w) (Z : Matrix (Fin n) (Fin r₀) E), (incM F Z).map (piInf τ) = Z.map τ.1 :=
    fun w τ Z => Matrix.ext fun i j => piInf_inclR τ (Z i j)
  have g3 : ∀ (w : InfinitePlace F) (τ : EmbOver E w) (s : Fin r₀ → ℝ),
      (Matrix.diagonal fun i => algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F (s i))).map (piInf τ) =
        Matrix.diagonal fun i => (s i : ℂ) := fun w τ s => by
    rw [Matrix.diagonal_map (map_zero _)]
    exact congrArg Matrix.diagonal (funext fun i => piInf_infScale h τ (s i))
  have key : ∀ {P Q : Matrix (Fin n) (Fin r₀) (AE F E)}, P.map ψ = Q.map ψ →
      (∀ (w : InfinitePlace F) (τ : EmbOver E w), P.map (piInf τ) = Q.map (piInf τ)) → P = Q :=
    fun hf hi => Matrix.ext fun i j => ae_ext h (congrFun (congrFun hf i) j) fun w τ => congrFun (congrFun (hi w τ) i) j
  refine ⟨key ?_ fun w τ => ?_, key ?_ fun w τ => ?_, fun z hz hz' => funext fun i => ae_ext h ?_ fun w τ => ?_⟩
  · rw [Matrix.map_mul, Matrix.map_mul, f1, f2 t, Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.map_mul, Matrix.map_mul, g1, g2, g3, (ha.2 w τ).1]
  · rw [Matrix.map_mul, Matrix.map_mul, f1, f2 (fun i => (t i)⁻¹), Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.map_mul, Matrix.map_mul, g1, g2, g3, (ha.2 w τ).2.1]
    congr 2
    funext i
    push_cast
    rfl
  · change ψ ((M *ᵥ _) i) = ψ _
    rw [RingHom.map_mulVec, f1, Matrix.one_mulVec]
    rfl
  · change piInf τ ((M *ᵥ _) i) = piInf τ _
    rw [RingHom.map_mulVec, g1]
    have e : (piInf τ ∘ fun i => inclR (F := F) (AF F) (z i)) = fun i => τ.1 (z i) := funext fun i => piInf_inclR τ (z i)
    rw [e, (ha.2 w τ).2.2 z hz hz', piInf_inclR]

end GlobalTheory.TorusMat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementArchimedeanMatrixForm
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay

namespace GlobalTheory.SiegelTorusMat

theorem eq_of_scales {n q : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {X Y : Matrix (Fin n) (Fin q) ℂ}
    {P Q : Matrix (Fin q) (Fin n) ℂ} {d e : Fin q → ℂ} (hX : A * X = X * Matrix.diagonal d)
    (hY : A * Y = Y * Matrix.diagonal e) (hZ : A * (1 - X * P - Y * Q) = 1 - X * P - Y * Q) :
    A = 1 + X * Matrix.diagonal (fun i => d i - 1) * P + Y * Matrix.diagonal (fun i => e i - 1) * Q := by
  have h : ∀ a : Fin q → ℂ, Matrix.diagonal (fun i => a i - 1) = Matrix.diagonal a - 1 := fun a => by
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
  rw [Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hX, hY, Matrix.mul_one,
    sub_sub, sub_eq_iff_eq_add] at hZ
  rw [h, h, hZ]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  abel

theorem inv_scales {n q : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (hBA : B * A = 1) {X : Matrix (Fin n) (Fin q) ℂ}
    {d e : Fin q → ℂ} (hde : ∀ i, d i * e i = 1) (hX : A * X = X * Matrix.diagonal d) :
    B * X = X * Matrix.diagonal e := by
  have h : X * Matrix.diagonal d * Matrix.diagonal e = X := by
    rw [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
    simp only [hde, Matrix.diagonal_one, Matrix.mul_one]
  conv_lhs => rw [← h, ← hX, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hBA, Matrix.one_mul]

theorem archMat_torus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (q : ℕ) (Xf Yf : Matrix (Fin n) (Fin q) E), GlobalTheory.SiegelSet.IsWittFrame σ J Xf Yf →
    ∀ (t : Fin q → ℝ), (∀ i, 0 < t i) → ∀ a : GAd σ J, GlobalTheory.SiegelSet.IsTorusElt σ J Xf Yf t a →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w),
      GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = (1 + (Xf).map τ.1 * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ) - 1) * (Formalism.UG.cT (σ : E →+* E) Yf * J).map τ.1 +
                   (Yf).map τ.1 * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹ - 1) * (Formalism.UG.cT (σ : E →+* E) Xf * J).map τ.1) ∧
      GlobalTheory.Orb.archMat σ J τ (projArch σ J w a⁻¹) = (1 + (Xf).map τ.1 * Matrix.diagonal (fun i => (((fun i => (t i)⁻¹) i : ℝ) : ℂ) - 1) * (Formalism.UG.cT (σ : E →+* E) Yf * J).map τ.1 +
                   (Yf).map τ.1 * Matrix.diagonal (fun i => (((fun i => (t i)⁻¹) i : ℝ) : ℂ)⁻¹ - 1) * (Formalism.UG.cT (σ : E →+* E) Xf * J).map τ.1) := by
  intro F E _ _ _ _ _ σ h n J hJ q X Y hW t ht a ha w τ
  have cc : ∀ Z : Matrix (Fin n) (Fin q) E, Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) Z) = Z :=
    fun Z => Matrix.ext fun i j => GlobalTheory.SiegelSet.sigma_sigma h _
  have hJ' : Formalism.UG.cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 _ _
  have yx : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := by
    have := congrArg (Formalism.UG.cT (σ : E →+* E)) hW.xy
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, hJ', Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  have xx := hW.xx
  have yy := hW.yy
  have xy := hW.xy
  obtain ⟨hX, hY, hz⟩ := ha.2 w τ
  generalize Formalism.UG.cT (σ : E →+* E) Y * J = P at *
  generalize Formalism.UG.cT (σ : E →+* E) X * J = Q at *
  have hBA : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a⁻¹) * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = 1 := by
    rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
  generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = A at *
  generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a⁻¹) = B at *
  have hQ : Q * (1 - X * P - Y * Q) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, xx, xy]; simp
  have hP : P * (1 - X * P - Y * Q) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, yx, yy]; simp
  have hZ0 : A * (1 - X * P - Y * Q).map τ.1 = (1 - X * P - Y * Q).map τ.1 := by
    generalize (1 - X * P - Y * Q) = Z at *
    ext i j
    exact congrFun (hz (fun k => Z k j) (funext fun k => congrFun (congrFun hQ k) j)
      (funext fun k => congrFun (congrFun hP k) j)) i
  have hm : (1 - X * P - Y * Q).map τ.1 = 1 - X.map τ.1 * P.map τ.1 - Y.map τ.1 * Q.map τ.1 := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← RingHom.mapMatrix_apply, map_sub, map_sub, map_one]
    rfl
  rw [hm] at hZ0
  have ht' : ∀ i, ((t i : ℝ) : ℂ) ≠ 0 := fun i => Complex.ofReal_ne_zero.2 (ht i).ne'
  refine ⟨eq_of_scales hX hY hZ0, eq_of_scales (inv_scales hBA (fun i => ?_) hX) (inv_scales hBA (fun i => ?_) hY) ?_⟩
  · rw [Complex.ofReal_inv, mul_inv_cancel₀ (ht' i)]
  · rw [Complex.ofReal_inv, inv_inv, inv_mul_cancel₀ (ht' i)]
  · conv_lhs => rw [← hZ0, ← Matrix.mul_assoc, hBA, Matrix.one_mul]

end GlobalTheory.SiegelTorusMat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
section
noncomputable section

namespace GlobalTheory.ArchSch

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

def ech (t : ℝ) : ℂ := Complex.exp (-(2 * Real.pi * Complex.I) * (t : ℂ))

def sch {Y : Type} [AddCommGroup Y] [Module ℝ Y] (β : LinearMap.BilinForm ℝ Y) (a b : Y) (f : Y → ℂ) : Y → ℂ :=
  fun x => ech (β x b + β a b / 2) * f (x + a)

variable (F : Type) [Field F] [NumberField F]

def arch {κ : Type} (v : κ → AF F) : κ → mixedEmbedding.mixedSpace F := fun i => evI F (v i)

def trP (κ : Type) [Fintype κ] : LinearMap.BilinForm ℝ (κ → mixedEmbedding.mixedSpace F) :=
  LinearMap.mk₂ ℝ (fun x y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i))
    (fun _ _ _ => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add])
    (fun _ _ _ => by simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, LinearMap.map_smul, smul_eq_mul])
    (fun _ _ _ => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add])
    (fun _ _ _ => by simp only [Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, LinearMap.map_smul, smul_eq_mul])

theorem mixedTracePairing_apply {κ : Type} [Fintype κ] (x y : κ → mixedEmbedding.mixedSpace F) :
    trP F κ x y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i) := rfl

def liftA (ξ : mixedEmbedding.mixedSpace F) : AF F :=
  LinearMap.inl F (Ainf F) (Af F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm ξ)

variable {F} {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d d₁ : ℕ} {X : Spc F E n}
  {W : Spc F E d} {W₁ : Spc F E d₁}

def lagSet (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) :
    Set ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :=
  {l | ∃ u ∈ iso0 (F := F) n H', At (evI F) u ∧ ∃ z : Matrix (Fin n) (Fin d₁) (AE F E), At (evI F) z ∧
    arch F (M₁.co.e z).1 = 0 ∧
    l = (arch F (M.co.e (u + incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)).1,
      arch F (M.co.e (u + incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)).2)}

end GlobalTheory.ArchSch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualLatticeBoundedDenominator
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory

theorem exists_den_traceDual_ringOfIntegers :
    ∀ {F : Type} [Field F] [NumberField F], ∃ D : ℕ, 0 < D ∧ ∀ ξ : F,
      (∀ o : 𝓞 F, ∃ z : ℤ, Algebra.trace ℚ F (ξ * o) = z) → ∃ o : 𝓞 F, (D : F) * ξ = o := by
  intro F _ _
  refine ⟨(NumberField.discr F).natAbs, Int.natAbs_pos.mpr (NumberField.discr_ne_zero F), ?_⟩
  intro ξ hξ
  have hint := GlobalTheory.discr_mul_isIntegral_of_traceDual F ξ hξ
  have hint' : IsIntegral ℤ (((NumberField.discr F).natAbs : F) * ξ) := by
    rcases Int.natAbs_eq (NumberField.discr F) with h | h
    · have : ((NumberField.discr F).natAbs : F) = (NumberField.discr F : F) := by
        have h' : ((NumberField.discr F).natAbs : ℤ) = NumberField.discr F := by omega
        rw [← Int.cast_natCast, h']
      rw [this]; exact hint
    · have : ((NumberField.discr F).natAbs : F) = -(NumberField.discr F : F) := by
        have h' : ((NumberField.discr F).natAbs : ℤ) = -(NumberField.discr F) := by omega
        rw [← Int.cast_natCast, h', Int.cast_neg]
      rw [this, neg_mul]; exact hint.neg
  exact ⟨⟨_, hint'⟩, rfl⟩

end GlobalTheory
end

