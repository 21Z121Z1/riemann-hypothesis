import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormsVanishingOffFramesLeSpanShortTheta
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0037
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1651
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1661
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightFunctionCompactLevelContinuous
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)

noncomputable section

open Pointwise

namespace GlobalTheory.ResLine.HtCont

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem inv_eigen {x : Matrix (Fin n) (Fin 1) E} {p : GAd σ J} {l : (AF F ⊗[F] E)ˣ}
    (hp : (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x) :
    (matHom _ σ J p⁻¹).1 * adMat F x = (l⁻¹).1 • adMat F x := by
  have h1 : (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have h2 : l.1 • ((matHom _ σ J p⁻¹).1 * adMat F x) = adMat F x := by
    rw [← Matrix.mul_smul, ← hp, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  calc _ = ((l⁻¹).1 * l.1) • ((matHom _ σ J p⁻¹).1 * adMat F x) := by rw [Units.inv_mul, one_smul]
    _ = _ := by rw [← smul_smul, h2]

theorem exists_col_ne {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E} (hW : IsWittFrame σ J X Y) :
    ∃ i, col X i 0 ≠ 0 := by
  by_contra hc
  push_neg at hc
  have h0 : ∀ j, X j 0 = 0 := fun j => hc j
  have := congrFun (congrFun hW.xy 0) 0
  simp [Matrix.mul_apply, Formalism.UG.cT, h0] at this

theorem isCompact_and_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), Data σ J X Y L a h →
    IsCompact (levelAll σ J L a : Set (GAd σ J)) ∧ Continuous h := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hS
  obtain ⟨hCM, -, -, hW, hA, hI1, hI2⟩ := hS
  haveI := hA.lat
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)
  have hK : IsCompact (levelAll σ J L a : Set (GAd σ J)) := GlobalTheory.Doubling.isCompact_levelAll hCM J L a
  refine ⟨hK, ?_⟩
  obtain ⟨i, hi⟩ := exists_col_ne hW
  set x := col X with hx
  have hm : Continuous fun g : GAd σ J => (matHom _ σ J g).1 :=
    Units.continuous_val.comp (isEmbedding_matHom _ σ J).continuous
  let Λ : GAd σ J → AF F ⊗[F] E := fun g =>
    ((matHom _ σ J g).1 * adMat F x) i 0 * inclR (F := F) (AF F) (x i 0)⁻¹
  have hΛ : Continuous Λ := ((hm.matrix_mul continuous_const).matrix_elem i 0).mul continuous_const
  have key : ∀ p (l : (AF F ⊗[F] E)ˣ), (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x → l.1 = Λ p := by
    intro p l hl
    have e := congrFun (congrFun hl i) 0
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply] at e
    simp only [Λ, e, mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, mul_one]
  let P : Set (GAd σ J) := {p | (matHom _ σ J p).1 * adMat F x = Λ p • adMat F x ∧ Λ p * Λ p⁻¹ = 1}
  have memP : ∀ p, (∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x) → p ∈ P := by
    rintro p ⟨l, hl⟩
    have e1 := key p l hl
    have e2 := key p⁻¹ l⁻¹ (inv_eigen hl)
    exact ⟨by rw [← e1]; exact hl, by rw [← e1, ← e2, Units.mul_inv]⟩
  have hPc : IsClosed P :=
    (isClosed_eq (hm.matrix_mul continuous_const) (hΛ.smul continuous_const)).inter
      (isClosed_eq (hΛ.mul (hΛ.comp continuous_inv)) continuous_const)
  let u : P → (AF F ⊗[F] E)ˣ := fun p => ⟨Λ p, Λ p.1⁻¹, p.2.2, by rw [mul_comm]; exact p.2.2⟩
  have hu : Continuous u := Units.continuous_iff.2
    ⟨hΛ.comp continuous_subtype_val, (hΛ.comp continuous_inv).comp continuous_subtype_val⟩
  let f : P → ℝ := fun p => (absE F E (u p) : ℝ)
  have hf : Continuous f := NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp hu)
  have hval : ∀ p : P, ∀ k ∈ levelAll σ J L a, h (p.1 * k) = f p := fun p k hk =>
    hI2 p.1 (u p) p.2.1 k hk
  rw [continuous_iff_isClosed]
  intro s hs
  have hpre : h ⁻¹' s = (Subtype.val '' (f ⁻¹' s)) * (levelAll σ J L a : Set (GAd σ J)) := by
    ext g; constructor
    · intro hg
      obtain ⟨p, l, hl, k, hk, rfl⟩ := hI1 g
      have hp : p ∈ P := memP p ⟨l, hl⟩
      refine ⟨p, ⟨⟨p, hp⟩, ?_, rfl⟩, k, hk, rfl⟩
      show f ⟨p, hp⟩ ∈ s
      rw [← hval ⟨p, hp⟩ k hk]; exact hg
    · rintro ⟨_, ⟨p, hp, rfl⟩, k, hk, rfl⟩
      show h (p.1 * k) ∈ s
      rw [hval p k hk]; exact hp
  rw [hpre]
  exact (hPc.isClosedEmbedding_subtypeVal.isClosedMap _ (hs.preimage hf)).mul_right_of_isCompact hK

end GlobalTheory.ResLine.HtCont

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTatePointDualBasis
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open Classical

namespace GlobalTheory.HTLat.Point

theorem smul_latTQuot_le_latT : ∀ {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (φ : E →+* C) (d : C) {n : ℕ} (r : Fin n → O) (a : Fin n → 𝓞 E), (∀ σ : E →+* C, ∑ k, algebraMap O C (r k) * σ (a k) = if σ = φ then d else 0) → ∀ {w : P.V}, w ∈ P.latTQuot (σ := fun ψ : E →+* C => embO P.integers ψ) (isSplitting_embO P.integers) φ → d • w ∈ P.latT := by
  intro p _ C _ _ _ _ O _ _ _ _ _ E _ _ _ P φ d n r a hsum w hw
  obtain ⟨y, hy, rfl⟩ := hw
  have hact : ∀ (b : 𝓞 E) (x : P.V), x ∈ P.latT → P.actV b x ∈ P.latT := by
    intro b x hx
    obtain ⟨s, rfl⟩ := hx
    induction s using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy
    | tmul c t => exact ⟨c ⊗ₜ P.actT b t, by rw [P.inclT_tmul, P.inclT_tmul]; rfl⟩
  have e : d • idem (isSplitting_embO P.integers) φ =
      ∑ k, algebraMap O C (r k) ⊗ₜ[ℤ] a k := (isSplitting_embO P.integers).1 (by
    ext ψ
    rw [map_smul, splitMap_idem, map_sum, Finset.sum_apply]
    simp only [splitMap_tmul, RingHom.comp_apply, algebraMap_embO, Pi.smul_apply, Pi.single_apply,
      smul_eq_mul]
    rw [hsum ψ]
    split_ifs <;> simp)
  change d • proj (isSplitting_embO P.integers) P.actV φ y ∈ P.latT
  rw [proj, ← LinearMap.smul_apply, ← map_smul, e, map_sum, LinearMap.sum_apply]
  refine P.latT.sum_mem fun k _ => ?_
  rw [tensorAction_tmul, algebraMap_smul]
  exact P.latT.smul_mem _ (hact _ _ hy)

end GlobalTheory.HTLat.Point
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolSub0LeSpanShortGenUpto
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

open GlobalTheory.Dict.Extend GlobalTheory.Dict.Pull

namespace GlobalTheory.LargeCover

section Pull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def PrincUpTo (X : Data E r) (M : ℕ) (la : Wt X.Ψ r) : Prop :=
  ∀ ga : GL (Fin r) E, IsUStab X.Gm X.Λ ga →
    (∀ v ∈ X.Λ, ∃ u ∈ X.Λ, (ga : Matrix (Fin r) (Fin r) E) *ᵥ v = v + M • u) →
      ∃ gb ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, bchar la b = 1 ∧ ∀ x, lact gb x = lact ga (rmul x b)

theorem conj_stab {X X' : Data E r} (hG : X'.Gm = X.Gm) {a g : GL (Fin r) E} {M : ℕ} (ha : IsUn X a) (hg : IsUn X g)
    (hfix : mapL g (mapL a X'.Λ) = mapL a X'.Λ)
    (hM : ∀ u ∈ mapL a X'.Λ, ∃ u' ∈ mapL a X'.Λ, (g : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u') :
    IsUStab X'.Gm X'.Λ (a⁻¹ * g * a) ∧
      ∀ v ∈ X'.Λ, ∃ u ∈ X'.Λ, ((a⁻¹ * g * a : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v = v + M • u := by
  have hc : mapL (a⁻¹ * g * a) X'.Λ = X'.Λ := by
    rw [mapL_mul, mapL_mul, hfix, ← mapL_mul, inv_mul_cancel, mapL_one]
  refine ⟨⟨?_, fun x => ?_⟩, fun v hv => ?_⟩
  · rw [hG]
    exact isUn_mul (isUn_mul (isUn_inv ha) hg) ha
  · rw [← mem_mapL (a := a⁻¹ * g * a), hc]
  · obtain ⟨u', ⟨w, hw, e⟩, hu⟩ := hM _ (mem_mapL.2 hv)
    have e' : (a : Matrix (Fin r) (Fin r) E) *ᵥ w = u' := e
    refine ⟨w, hw, ?_⟩
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hu, ← e',
      Matrix.mulVec_add, Matrix.mulVec_smul, inv_mulVec, inv_mulVec]

theorem exists_pow_root_eq_one (K : Type) [Field K] [NumberField K] :
    ∃ w : ℕ, 0 < w ∧ ∀ (u : K) (n : ℕ), 0 < n → u ^ n = 1 → u ^ w = 1 := by
  refine ⟨NumberField.Units.torsionOrder K, NumberField.Units.torsionOrder_pos K, fun u n hn hu => ?_⟩
  have hi : IsIntegral ℤ u := IsIntegral.of_pow hn (hu ▸ isIntegral_one)
  have h1 : (⟨u, hi⟩ : 𝓞 K) ^ n = 1 := Subtype.ext hu
  let v : (𝓞 K)ˣ := Units.ofPowEqOne _ n h1 hn.ne'
  have hv : v ∈ NumberField.Units.torsion K :=
    (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, Units.pow_ofPowEqOne h1 hn.ne'⟩)
  have h2 : (⟨v, hv⟩ : NumberField.Units.torsion K) ^ NumberField.Units.torsionOrder K = 1 := by
    unfold NumberField.Units.torsionOrder
    first | exact pow_card_eq_one | exact pow_card_eq_one'
  have h3 : v ^ NumberField.Units.torsionOrder K = 1 := congrArg Subtype.val h2
  exact congrArg (fun x : (𝓞 K)ˣ => ((x : 𝓞 K) : K)) h3

theorem princUpTo_of_root (X : Data E r) (M w : ℕ) (hw : ∀ (u : E) (n : ℕ), 0 < n → u ^ n = 1 → u ^ w = 1)
    (la : Wt X.Ψ r) (hla : ∀ τ i, (w : ℤ) ∣ la τ i)
    (h : ∀ ga : GL (Fin r) E, IsUStab X.Gm X.Λ ga →
      (∀ x ∈ X.Λ, ∃ y ∈ X.Λ, (ga : Matrix (Fin r) (Fin r) E) *ᵥ x - x = (M : E) • y) →
      ∃ gb ∈ X.Γ, ∃ (u : E) (n : ℕ), 0 < n ∧ u ^ n = 1 ∧
        (gb : Matrix (Fin r) (Fin r) E) = u • (ga : Matrix (Fin r) (Fin r) E)) : PrincUpTo X M la := by
  intro ga hga hc
  obtain ⟨gb, hgb, u, n, hn, hu, he⟩ := h ga hga fun x hx => by
    obtain ⟨y, hy, e⟩ := hc x hx
    exact ⟨y, hy, by rw [e, add_sub_cancel_left, Nat.cast_smul_eq_nsmul]⟩
  have hu0 : u ≠ 0 := by rintro rfl; rw [zero_pow hn.ne'] at hu; exact zero_ne_one hu
  let b : Frame X.Ψ r := fun τ => (Matrix.diagonal fun _ => τ.1 u : Matrix (Fin r) (Fin r) ℂ)
  have hb : ∀ τ, mat b τ = τ.1 u • (1 : Matrix (Fin r) (Fin r) ℂ) := fun τ => by
    rw [Matrix.smul_one_eq_diagonal]; rfl
  refine ⟨gb, hgb, b, fun τ => ⟨?_, fun a c hac => Matrix.diagonal_apply_ne _ hac.ne'⟩, ?_, fun x => ?_⟩
  · rw [hb, Matrix.det_smul, Matrix.det_one, _root_.mul_one]
    exact pow_ne_zero _ ((map_ne_zero τ.1).2 hu0)
  · refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun i _ => ?_
    obtain ⟨k, hk⟩ := hla τ i
    have : b τ i i = τ.1 u := Matrix.diagonal_apply_eq _ i
    rw [this, hk, _root_.zpow_mul, zpow_natCast, ← map_pow, hw u n hn hu, map_one, _root_.one_zpow]
  · funext τ
    show (gb : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ =
      (ga : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ)
    have : (u • (ga : Matrix (Fin r) (Fin r) E)).map τ.1 = τ.1 u • (ga : Matrix (Fin r) (Fin r) E).map τ.1 := by
      ext a c; simp
    rw [he, this, hb, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul]

end Pull

theorem isStabForm_pull_upto (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X' X : Data E r) (h : SameSp X' X) (ga : GL (Fin r) E) (la' : Wt X'.Ψ r) (la : Wt X.Ψ r) (Δ : Subgroup (GL (Fin r) E)) (M : ℕ) (P : Frame X'.Ψ r → ℂ) (hga : IsUn X ga) (hl : ∀ (τ : X.Ψ) i, la τ i = la' ⟨τ.1, by rw [h.psi]; exact τ.2⟩ i) (hΔ : ∀ g' ∈ Δ, IsUn X g' ∧ (mapL g' (mapL ga X'.Λ) = mapL ga X'.Λ → ∀ u ∈ mapL ga X'.Λ, ∃ u' ∈ mapL ga X'.Λ, (g' : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u')) (hP : PrincUpTo X' M la') (hχ : ChiOne X' la') (hb : X'.IsBddSec la' P) : IsStabForm X Δ (mapL ga X'.Λ) la (fun x => P (castFr h.psi.symm (lact ga⁻¹ x))) ∧ ∀ x ∈ X'.dom, lact ga (castFr h.psi x) ∈ X.dom ∧ castFr h.psi.symm (lact ga⁻¹ (lact ga (castFr h.psi x))) = x := by
  obtain ⟨⟨hd, hbor, hinv⟩, C, hC⟩ := hb
  have m1 : ∀ x ∈ X.dom, castFr h.psi.symm (lact ga⁻¹ x) ∈ X'.dom := fun x hx =>
    cast_GG h.psi.symm h.gm.symm h.p0.symm (lact_mem (isUn_inv hga) hx)
  have m2 : ∀ x ∈ X'.dom, lact ga (castFr h.psi x) ∈ X.dom := fun x hx =>
    lact_mem hga (cast_GG h.psi h.gm h.p0 hx)
  refine ⟨⟨?_, ?_, ?_, C, ?_⟩, fun x hx => ⟨m2 x hx, ?_⟩⟩
  · exact hd.comp ((cast_diff h.psi.symm).comp (differentiable_lact ga⁻¹)).differentiableOn m1
  · intro x hx b hb
    rw [lact_rmul, cast_rmul, hbor _ (m1 x hx) _ (cast_bor h.psi.symm hb), ← cast_bchar h.psi hl]
    rfl
  · intro g hg hfix x hx
    obtain ⟨s1, s2⟩ := conj_stab h.gm hga (hΔ g hg).1 hfix ((hΔ g hg).2 hfix)
    obtain ⟨gb, hgb, b, hb, hb1, hgbb⟩ := hP _ s1 s2
    have e : lact ga⁻¹ (lact g x) = lact (ga⁻¹ * g * ga) (lact ga⁻¹ x) := by
      rw [lact_lact, lact_lact, mul_inv_cancel_right]
    show P (castFr h.psi.symm (lact ga⁻¹ (lact g x))) = _
    have e2 := hinv _ hgb _ (m1 x hx)
    rw [hχ _ hgb, _root_.one_mul, hgbb, lact_rmul, hbor _ (lact_mem s1.1 (m1 x hx)) _ hb, hb1, _root_.one_mul] at e2
    rw [e, cast_lact, e2]
  · intro x hx
    refine le_of_eq_of_le ?_ (hC _ (m1 x hx))
    unfold Data.pnorm
    rw [cast_wt h.psi h.gm hl]
    simp only [dmin_lact (isUn_inv hga)]
  · rw [lact_lact, inv_mul_cancel, lact_one, cast_symm]

set_option maxHeartbeats 800000 in

theorem holSub0_le_span_shortGen_upto : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → l.A = 1 → (∀ k k', (U.X k).Gm = (U.X k').Gm ∧ (U.X k).ξ0 = (U.X k').ξ0) → d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → UnitC d → ¬ 3 ∣ d.pd → (Dw.p + Dw.q ≤ n → ∃ ph ψ x₀, d.PhiPin ph ψ x₀) → ∀ (nab : NabV Xo c) (bad nV : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < bad → Dom a n → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → (∀ k, PrincUpTo (U.X k) l.M (Formalism.L2.PjFree.laU U a n k)) → (∀ k, ChiOne (U.X k) (Formalism.L2.PjFree.laU U a n k)) → ShortValTot Xo c nab bad nV a n d → holSub0 U.X (Formalism.L2.PjFree.laU U a n) ≤ Submodule.span ℂ (Formalism.L2.PjFree.rdU U '' shortGen Xo c nab bad nV a n d) := by
  intro hci E _ _ _ H Dw l Xo c n d σ r U hσ hU hr1 hA hG hlev hnab huc h3 hpin nab bad nV a hbad hdom hbig
    hpr hchi htot P hP
  obtain ⟨hP1, hP0⟩ := hP
  rcases isEmpty_or_nonempty U.Comp with hemp | ⟨⟨k₀⟩⟩
  · have : P = 0 := funext fun k => (hemp.false k).elim
    rw [this]
    exact Submodule.zero_mem _
  obtain ⟨W⟩ := nonempty_uw hU
  have hrpq : r = Dw.p + Dw.q := hU.1
  have hn : r ≤ n := by
    have := Module.finrank_pos (R := ℚ) (M := E)
    nlinarith
  have hev : Even n := by
    unfold Formalism.L2.Pj.Dom at hdom
    tauto
  have huw := GlobalTheory.T.uniformisation_component_lattices_markings E H Dw l Xo c σ r U hσ hU hr1 W
  have hsame : ∀ k, SameSp (U.X k) (U.X k₀) := fun k =>
    ⟨Finset.ext fun τ => ((hU.2.1 k).2 τ).trans ((hU.2.1 k₀).2 τ).symm, (hG k k₀).1,
      (hU.2.1 k).1.trans (hU.2.1 k₀).1.symm, (hG k k₀).2, by rw [(huw k).1, (huw k₀).1, (hG k k₀).2]⟩
  obtain ⟨ph, ψ, x₀, hph⟩ := hpin (hrpq ▸ hn)
  obtain ⟨Dc, hDe, -⟩ := GlobalTheory.T.exists_letterRowWeightDictionary E H Dw l c σ r W.g n (U.X k₀) a W.e hσ hrpq (hU.2.1 k₀).1 (hU.2.1 k₀).2
    (huw k₀).2.1 hdom
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_classicalLevelData_coverSelfDual E H Dw l Xo c n d σ r (U.X k₀) hn hrpq (huw k₀).2.1 hlev h3 ph ψ x₀ hph
  obtain ⟨v₀, mu, hv₀, hmu⟩ := GlobalTheory.SW.exists_vacua_and_multipliers E r (U.X k₀) W.g Dc.bas Dc.idx n Dc.sympl hev D
  obtain ⟨x0, ga, δ, hadm, hset, hsep⟩ := GlobalTheory.T.exists_components_lattices_moved_to_level_family E H Dw l Xo c n d σ r U hσ hU hr1 hA hlev W k₀ hsame ph D hn hD
  obtain ⟨u, hu, hread⟩ := GlobalTheory.T.short_series_readings_eq_classical_thetaSeries hci E H Dw l Xo c n d σ r U hσ hU hr1 hlev hnab huc ph ψ x₀ hph W (U.X k₀) a
    hdom Dc D hn hDe hD v₀ hv₀ x0
  choose C hC hrd using fun k => hread k (hsame k) (ga k) (δ k) (hset k).1 (hset k).2.1 (hset k).2.2.1
    (hset k).2.2.2.1 (hset k).2.2.2.2
  have hmu1 := GlobalTheory.T.vacuum_multiplier_eq_one_on_stabiliser E H Dw l Xo c n d σ r W.g (U.X k₀) Dc.bas Dc.idx D hn ph Dc.sympl hev hD
    (W.F.Di (W.ik k₀)) (W.emb k₀) (huw k₀).2.2.2.1 (huw k₀).2.2.2.2.1 (huw k₀).2.2.2.2.2.1 (huw k₀).2.2.2.2.2.2
    v₀ hv₀ mu hmu
  have hgrp := (GlobalTheory.SW.level_laws E r (U.X k₀) W.g Dc.bas Dc.idx n Dc.sympl hev D hn).2.2.1
  have hpull := fun k => isStabForm_pull_upto E r (U.X k) (U.X k₀) (hsame k) (ga k) (Formalism.L2.PjFree.laU U a n k)
    (wtOf (U.X k₀) Dc.hr Dc.k Dc.k' n) D.grp l.M ((C k)⁻¹ • P k) (hset k).1
    (fun τ i => by
      rw [Dc.wt_eq]
      simp only [wtX, Formalism.L2.PjFree.laU, (hsame k).p0])
    (fun g' hg' => ⟨((hgrp g').1 hg').1, fun hfix => (hmu1 _ (hset k).2.1 g' hg' hfix).2⟩)
    (hpr k) (hchi k) (isBddSec_of_mem_holSub U.X _ P hP1 k _)
  have hM2 : 0 < d.l₂.M := lt_of_lt_of_le (by norm_num) d.l₂.three_le
  have hMm : ((2 * bad * d.l₂.M : ℕ) : 𝓞 E) ∈ D.𝔪 := by
    rw [hD.m, Nat.cast_mul]
    refine Ideal.mul_mem_left _ _ ?_
    have h1 : (d.l₂.M : 𝓞 E) ∈ d.l₂.Mb * d.l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [d.l₂.prod]
      exact Ideal.mem_span_singleton_self _
    unfold Mfr
    exact (Submodule.mem_inf.1 (Ideal.mul_le_inf h1)).2
  obtain ⟨m, Λ, Pj, hΛ, hQ⟩ := GlobalTheory.T.stableForms_eq_sum_thetaSeries_freeLowerRows E r (U.X k₀) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hev hbig D hn
    (2 * bad * d.l₂.M) (Mfr l) (Jd d) (by positivity) hMm hD.prod hD.cop v₀ hv₀ mu hmu Dc.k Dc.k' U.Comp
    (fun k => mapL (ga k) (U.X k).Λ) _ (fun k => (hset k).2.1) hsep
    (fun k g' hg' hfix => (hmu1 _ (hset k).2.1 g' hg' hfix).1) (fun k => (hpull k).1)
  have hgl := fun j => GlobalTheory.Dict.GenLatCmp.genLat_vset E n (Λ j)
  have hg1 := fun j => (hgl j).1 bad d.l₂.M hbad d.l₂.odd (hΛ j).1
  choose N hN using fun j => (hg1 j).2.2.2
  have hV : ∀ j, Λ j ∈ Vset E n d.l₂.M := fun j => (hgl j).2.2.1 _ _ (Dvd.intro_left _ rfl) (hΛ j).1
  choose mj t R hR hPj using fun j => GlobalTheory.T.harmonicRowHighest_eq_span_integral_harmonic E H Dw l c σ r W.g Dw.p n (U.X k₀) a Dc (Λ j) (N j)
    (hN j).1.pos ((hN j).2.2.trans inf_le_left) (Pj j) (hΛ j).2
  choose f hf hfr using fun j i => (htot ⟨Λ j⟩ (N j) x0 (R j i) (hg1 j).1 (hg1 j).2.1 (hg1 j).2.2.1 (hN j)
    (hadm _) (hR j i)).2
  have hPe : P = ∑ j, ∑ i, (t j i * (u (Λ j) (N j))⁻¹) • Formalism.L2.PjFree.rdU U (f j i) := by
    funext k x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hx : x ∈ (U.X k).dom
    · obtain ⟨hx1, hx2⟩ := (hpull k).2 x hx
      have e1 := hQ k _ hx1
      rw [hx2, Pi.smul_apply, smul_eq_mul, inv_mul_eq_iff_eq_mul₀ (hC k)] at e1
      rw [e1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hPj j, theta_sum_smul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hrd k (Λ j) (hV j) (N j) (hN j) (R j i) (hR j i).1 (f j i) (hf j i) (hfr j i) x hx]
      have := hu (Λ j) (hV j) (N j) (hN j)
      field_simp
    · rw [hP0 k x hx]
      refine (Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun i _ => ?_).symm
      have : Formalism.L2.PjFree.rdU U (f j i) k x = 0 := dif_neg hx
      rw [this, mul_zero]
  rw [hPe]
  refine Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨f j i, ⟨hf j i, ⟨Λ j⟩, N j, x0, R j i, (hg1 j).1, (hg1 j).2.1, (hg1 j).2.2.1, hN j,
    hadm _, hR j i, hfr j i⟩, rfl⟩

end GlobalTheory.LargeCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDelPullbackFderivFormEqZero
section
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)

namespace GlobalTheory.CxForm.DelVanish

variable {n : ℕ}

theorem delAt_const (c : Alt n) (v : V n) : delAt (fun _ => c) v = 0 := by
  simp [delAt, coefwise]

theorem delAt_add {F G : V n → Alt n} {v : V n}
    (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    delAt (fun x => F x + G x) v = delAt F v + delAt G v := by
  have key (a : Fin n) : coefwise (fun f => del f v (coordVec a)) (fun x => F x + G x) =
      coefwise (fun f => del f v (coordVec a)) F + coefwise (fun f => del f v (coordVec a)) G := by
    simp only [coefwise, ← Finset.sum_add_distrib, ← add_smul]
    refine Finset.sum_congr rfl fun S _ => ?_
    simp only [map_add, Finsupp.add_apply]
    rw [del_add (hF S) (hG S), ContinuousLinearMap.add_apply]
  simp only [delAt, key, mul_add, Finset.sum_add_distrib]

theorem repr_ι (x : Fin n ⊕ Fin n → ℂ) (S : Finset (Fin (n + n))) :
    (bas n).repr (ExteriorAlgebra.ι ℂ x) S =
      ∑ i, x i * (bas n).repr (ExteriorAlgebra.ι ℂ (Pi.single i 1)) S := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  simp only [map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (Pi.single i (x i) : Fin n ⊕ Fin n → ℂ) = x i • Pi.single i 1 by
    ext j; simp [Pi.single_apply]]
  simp

theorem del_mul_const {f : V n → ℂ} {v : V n} (hf : DifferentiableAt ℝ f v) (k : ℂ) (e : V n) :
    del (fun w => f w * k) v e = del f v e * k := by
  rw [del_mul hf (differentiableAt_const k), del_const]; simp

theorem delAt_ι {u : V n → (Fin n ⊕ Fin n → ℂ)} {v : V n}
    (hu : ∀ i, DifferentiableAt ℝ (fun w => u w i) v) :
    delAt (fun w => ExteriorAlgebra.ι ℂ (u w)) v =
      ∑ a, dz a * ExteriorAlgebra.ι ℂ (fun i => del (fun w => u w i) v (coordVec a)) := by
  refine Finset.sum_congr rfl fun a _ => congrArg _ ((bas n).ext_elem fun S => ?_)
  have e : (fun x => (bas n).repr (ExteriorAlgebra.ι ℂ (u x)) S) = fun x =>
      ∑ i, u x i * (bas n).repr (ExteriorAlgebra.ι ℂ (Pi.single i 1)) S := funext fun x => repr_ι _ _
  rw [FormMul.repr_coefwise, repr_ι, e]
  rw [del_sum (fun i _ => (hu i).mul_const _), ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ => del_mul_const (hu i) _ _

theorem sum_symm_dz_mul (s : Fin n → Fin n → ℂ) (hs : ∀ a b, s a b = s b a) :
    ∑ a, ∑ b, s a b • (dz a * dz b) = 0 := by
  set X := ∑ a, ∑ b, s a b • (dz a * dz b) with hX
  have h : X = -X := by
    conv_lhs => rw [hX, Finset.sum_comm]
    simp only [hX, ← Finset.sum_neg_distrib, ← smul_neg]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hs, dz, dz, eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)]
  have h2 : (2 : ℂ) • X = 0 := by
    rw [two_smul]; nth_rewrite 2 [h]; exact add_neg_cancel X
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

theorem delAt_pull_fderiv_ι {φ : V n → V n} {v : V n} (hφ : ContDiffAt ℂ 2 φ v) (m : Fin n ⊕ Fin n → ℂ) :
    delAt (fun w => pull (fderiv ℂ φ w) (ExteriorAlgebra.ι ℂ m)) v = 0 := by
  have hJ : DifferentiableAt ℂ (fderiv ℂ φ) v :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hE (b c : Fin n) : DifferentiableAt ℂ (fun w => fderiv ℂ φ w (coordVec b) c) v :=
    by
      have := (EuclideanSpace.proj (𝕜 := ℂ) c).differentiableAt.comp v
        (hJ.clm_apply (differentiableAt_const (coordVec b)))
      simpa [Function.comp_def] using this
  have hEr (b c : Fin n) : DifferentiableAt ℝ (fun w => fderiv ℂ φ w (coordVec b) c) v :=
    (hE b c).restrictScalars ℝ
  have hEc (b c : Fin n) : DifferentiableAt ℝ (fun w => conj (fderiv ℂ φ w (coordVec b) c)) v := by
    have := Complex.conjCLE.differentiableAt.comp v (hEr b c)
    simpa [Function.comp_def] using this
  have hdel (a b c : Fin n) : del (fun w => fderiv ℂ φ w (coordVec b) c) v (coordVec a) =
      fderiv ℂ (fderiv ℂ φ) v (coordVec a) (coordVec b) c := by
    have := del_clm_comp ((EuclideanSpace.proj c).comp (ContinuousLinearMap.apply ℂ (V n) (coordVec b)))
      (hJ.restrictScalars ℝ) (coordVec a)
    rw [del_eq_fderiv hJ] at this
    exact this
  have hdelc (a b c : Fin n) : del (fun w => conj (fderiv ℂ φ w (coordVec b) c)) v (coordVec a) = 0 := by
    rw [del_conj, dbar_eq_zero (hE b c)]; simp
  have hsymm : IsSymmSndFDerivAt ℂ φ v := hφ.isSymmSndFDerivAt (by simp)
  have hF : (fun w => pull (fderiv ℂ φ w) (ExteriorAlgebra.ι ℂ m)) = fun w => ExteriorAlgebra.ι ℂ
      (Sum.elim (fun b => ∑ c, fderiv ℂ φ w (coordVec b) c * m (.inl c))
        (fun b => ∑ c, conj (fderiv ℂ φ w (coordVec b) c) * m (.inr c))) := by
    funext w
    rw [pull, ExteriorAlgebra.map_apply_ι]
    congr 1
    funext i
    rcases i with b | b <;> simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  have hu : ∀ i, DifferentiableAt ℝ (fun w => Sum.elim (fun b => ∑ c, fderiv ℂ φ w (coordVec b) c * m (.inl c))
      (fun b => ∑ c, conj (fderiv ℂ φ w (coordVec b) c) * m (.inr c)) i) v := by
    rintro (b | b)
    · simpa using DifferentiableAt.fun_sum (u := Finset.univ) fun c _ => (hEr b c).mul_const (m (.inl c))
    · simpa using DifferentiableAt.fun_sum (u := Finset.univ) fun c _ => (hEc b c).mul_const (m (.inr c))
  set s : Fin n → Fin n → ℂ := fun a b => ∑ c, fderiv ℂ (fderiv ℂ φ) v (coordVec a) (coordVec b) c * m (.inl c)
    with hs
  have hw (a : Fin n) : (fun i => del (fun w => Sum.elim (fun b => ∑ c, fderiv ℂ φ w (coordVec b) c * m (.inl c))
      (fun b => ∑ c, conj (fderiv ℂ φ w (coordVec b) c) * m (.inr c)) i) v (coordVec a)) =
      ∑ b, s a b • Pi.single (Sum.inl b) 1 := by
    funext i
    rcases i with b | b
    · simp only [Sum.elim_inl]
      rw [del_sum (fun c _ => (hEr b c).mul_const _), ContinuousLinearMap.sum_apply]
      simp [del_mul_const (hEr _ _), hdel, Finset.sum_apply, Pi.single_apply, hs]
    · simp only [Sum.elim_inr]
      rw [del_sum (fun c _ => (hEc b c).mul_const _), ContinuousLinearMap.sum_apply]
      simp [del_mul_const (hEc _ _), hdelc, Finset.sum_apply, Pi.single_apply]
  rw [hF, delAt_ι hu]
  simp only [hw, map_sum, map_smul, Finset.mul_sum, mul_smul_comm]
  exact sum_symm_dz_mul s fun a b => by simp only [hs, hsymm (coordVec a) (coordVec b)]

theorem delAt_pull_fderiv : ∀ {n : ℕ} {φ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n} {v : ReciprocityTheory.L2DbarEstimates.V n},
    ContDiffAt ℂ 2 φ v → ∀ γ : GlobalTheory.CxForm.Alt n,
      GlobalTheory.CxForm.delAt (fun w => GlobalTheory.CxForm.pull (fderiv ℂ φ w) γ) v = 0 := by
  intro n φ v hφ γ
  have hD := fun γ S => GlobalTheory.CxForm.differentiableAt_repr_pull_fderiv hφ γ S
  induction γ using ExteriorAlgebra.induction with
  | algebraMap r => simp only [AlgHom.commutes]; exact delAt_const _ _
  | ι m => exact delAt_pull_fderiv_ι hφ m
  | mul a b ha hb =>
    obtain ⟨y, hy⟩ := FormMul.delAt_mul (hD a) (hD b)
    simp only [map_mul]
    rw [hy, ha, hb, zero_mul, mul_zero, add_zero]
  | add a b ha hb =>
    simp only [map_add]
    rw [delAt_add (hD a) (hD b), ha, hb, add_zero]

end GlobalTheory.CxForm.DelVanish
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteTorsionUnramifiedOfTateModuleUnramifiedStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinite_torsionUnramified_of_tateModuleUnramified : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (l : ℕ) [Fact l.Prime], (l : ResidueField R) ≠ 0 → TateUnramified A V l → {m : ℕ | (m : ResidueField R) ≠ 0 ∧ TorsionUnramified A V m}.Infinite := by
  first | exact @GlobalTheory.AbVarRed.infinite_torsionUnramified_of_tateUnramified | exact GlobalTheory.AbVarRed.infinite_torsionUnramified_of_tateUnramified | (intros; apply GlobalTheory.AbVarRed.infinite_torsionUnramified_of_tateUnramified <;> assumption)
end

