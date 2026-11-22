import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1671
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2506
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1717
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1814
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2365
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2485
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0018
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2491
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2492
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2404
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0043
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularKodairaSpencerCoordinateAffineOffBo
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CompHS
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open scoped Classical
open GlobalTheory.AllWt (exOf)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw))

theorem glue_field_cover {Z : Scheme.{0}} [IsReduced Z] (V : Z.Opens)
    (R : ∀ (L : Type) [Field L], (Sp L ⟶ Z) → L → Prop)
    (loc : ∀ p ∈ V, ∃ (W : Z.Opens) (a : Γ(Z, W)), p ∈ W ∧ W ≤ V ∧
      (∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ W), R L z (ev z W hz a)) ∧
      ∀ (L : Type) [Field L] (z : Sp L ⟶ Z), ⊤ ≤ z ⁻¹ᵁ W → ∀ x y, R L z x → R L z y → x = y) :
    ∃ a : Γ(Z, V), ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ V), R L z (ev z V hz a) := by
  choose! W a hp hWV ha hu using loc
  let I := {p // p ∈ V}
  have hc : ∀ p ∈ V, ∃ i : I, p ∈ W i.1 := fun p h => ⟨⟨p, h⟩, hp p h⟩
  obtain ⟨s, hs, -⟩ := Z.sheaf.existsUnique_gluing' (fun i : I => W i.1) V (fun i => homOfLE (hWV i.1 i.2))
    (fun p h => TopologicalSpace.Opens.mem_iSup.2 (hc p h)) (fun i => a i.1) (fun i j => by
      refine GlobalTheory.FlagMod.ext_ev_field (a := resG Z inf_le_left (a i.1)) (b := resG Z inf_le_right (a j.1)) fun L _ z hz => ?_
      have hi := le_preimage_mono inf_le_left hz
      have hj := le_preimage_mono inf_le_right hz
      rw [GlobalTheory.FlagMod.ev_res z _ hz hi, GlobalTheory.FlagMod.ev_res z _ hz hj]
      exact hu i.1 i.2 L z hi _ _ (ha i.1 i.2 L z hi) (ha j.1 j.2 L z hj))
  refine ⟨s, fun L _ z hz => ?_⟩
  obtain ⟨i, hi⟩ := hc (z (IsLocalRing.closedPoint L)) (hz (Set.mem_univ _))
  have hi' : ⊤ ≤ z ⁻¹ᵁ W i.1 := ((IsLocalRing.closed_point_mem_iff (U := z ⁻¹ᵁ W i.1)).1 hi).ge
  have e : ev z V hz s = ev z (W i.1) hi' (a i.1) :=
    (GlobalTheory.FlagMod.ev_res z (hWV i.1 i.2) hi' hz s).symm.trans (congrArg _ (hs i))
  exact e ▸ ha i.1 i.2 L z hi'

theorem exists_local (hP : GlobalTheory.Published.AbelianDeRham)
    (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y)
    (i : M.K.bundle.ι) (k : X.F.J) (W : M.X.Opens) (hW : W ≤ ksOpen M i k) (p : M.X) (hp : p ∈ W) :
    ∃ (W' : M.X.Opens) (a : Γ(M.X, W')), p ∈ W' ∧ W' ≤ W ∧
      (∀ (L : Type) [Field L] (z : Sp L ⟶ M.X) (hz : ⊤ ≤ z ⁻¹ᵁ W'), KSRel M i k z (ev z W' hz a)) ∧
      ∀ (L : Type) [Field L] (z : Sp L ⟶ M.X), ⊤ ≤ z ⁻¹ᵁ W' → ∀ x y, KSRel M i k z x → KSRel M i k z y → x = y := by
  have hWk : ksOpen M i k ≤ M.off ⊓ (toFlag M) ⁻¹ᵁ X.F.U k := fun s hs =>
    ⟨hs.1, (((common₀ X Z).pull M.σ).mem _ _ _).1 hs.2.2⟩
  have hWi : ksOpen M i k ≤ M.K.bundle.U i := fun s hs => hs.2.1
  obtain ⟨V, f, hpV, hf⟩ := exists_isFrame_dOn M.str (dimFlag Dw) p
  obtain ⟨W₁, hW₁, hpW₁, hW₁V⟩ := Opens.isBasis_iff_nbhd.1 M.X.isBasis_affineOpens (show p ∈ W ⊓ V from ⟨hp, hpV⟩)
  obtain ⟨W', hW', eH, hpW', hWW', eH1, eH2⟩ := GlobalTheory.T.hodge_de_rham_on_modification_of_flag_cover M hP hKS k W₁
    ((hW₁V.trans inf_le_left).trans (hW.trans hWk)) p hpW₁
  have hWV : W' ≤ W := hWW'.trans (hW₁V.trans inf_le_left)
  have hW'k : W' ≤ M.off ⊓ (toFlag M) ⁻¹ᵁ X.F.U k := hWV.trans (hW.trans hWk)
  have hW'i : W' ≤ M.K.bundle.U i := hWV.trans (hW.trans hWi)
  obtain ⟨eV, eV1, eV2⟩ := GlobalTheory.T.exists_ringMaps_lift_vertical_deformations_affine M k W' hW' hW'k
  let e : TIx Dw (psiSet H) → (Γ(M.X, W') →+* DualNumber Γ(M.X, W')) := Sum.elim eH eV
  have e1 : ∀ b s, (e b s).fst = s := by
    rintro (b | b) s
    · exact eH1 b s
    · exact eV1 b s

  have e2 : ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W') →+* K)
      (hk : ⊤ ≤ ((spMap ψ ≫ tau hW') ≫ toFlag M) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c K),
      X.F.ChartFr k _ hk Q → ∃ v, IsTanFrame (psiSet H) Q v ∧
        ∀ b, spMap ((dualMap ψ).comp (e b)) ≫ tau hW' ≫ toFlag M = X.ptY (v b) := by
    intro K _ _ ψ hk Q hQ
    choose w₁ hw₁ hw₁' hw₁'' using eH2 K ψ hk Q hQ
    choose w₂ hw₂ hw₂' using eV2 K ψ hk Q hQ
    refine ⟨Sum.elim w₁ w₂, ⟨fun b => ⟨hw₁ b, hw₁' b⟩, fun b => hw₂ b⟩, ?_⟩
    rintro (b | b)
    · exact hw₁'' b
    · exact hw₂' b
  let g : Fin (dimFlag Dw) → Γ(M.X, W') := fun a => resG M.X (hWW'.trans (hW₁V.trans inf_le_right)) (f a)
  have hu : IsUnit (M.K.jacobian i hW'i g) := (M.K.isUnit_jacobian_iff i hW' hW'i g).2 (by
    have := hf.res hW' (hWW'.trans (hW₁V.trans inf_le_right))
    rwa [resForm_dOn] at this)
  let A : Matrix (Fin (dimFlag Dw)) (Fin (dimFlag Dw)) Γ(M.X, W') :=
    Matrix.of fun a b => (e (tanOrd Dw b) (g a)).snd

  let zv : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X) :=
    fun ψ b => spMap ((dualMap ψ).comp (e b)) ≫ tau hW'
  have hzvW : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K) b, ⊤ ≤ zv ψ b ⁻¹ᵁ W' := fun ψ b =>
    le_preimage_comp _ (tau_le hW' le_rfl)
  have hred : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K) b,
      spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ zv ψ b = spMap ψ ≫ tau hW' := fun {K} _ ψ b => by
    simp only [zv]
    rw [← Category.assoc, ← spMap_comp]
    congr 2
    ext s
    simp [dualMap, e1]
  have hev : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K) a b,
      (evalPt (zv ψ b) W' (hzvW ψ b) (g a)).snd = ψ (e b (g a)).snd := fun ψ a b => by
    have := ev_spMap_tau hW' ((dualMap ψ).comp (e b)) (hzvW ψ b)
    have h2 : evalPt (zv ψ b) W' (hzvW ψ b) (g a) = ((dualMap ψ).comp (e b)) (g a) := congrFun (congrArg DFunLike.coe this) _
    rw [h2]
    simp [dualMap]
  have hdet : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K),
      (Matrix.of fun a b => (evalPt (zv ψ (tanOrd Dw b)) W' (hzvW ψ _) (g a)).snd).det = ψ A.det := fun ψ => by
    rw [RingHom.map_det]
    congr 1
    ext a b
    exact hev ψ a _
  have hzW : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), ⊤ ≤ (spMap ψ ≫ tau hW') ⁻¹ᵁ W' := fun ψ =>
    le_preimage_comp _ (tau_le hW' le_rfl)
  have ho : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), ⊤ ≤ (spMap ψ ≫ tau hW') ⁻¹ᵁ M.off := fun ψ =>
    le_preimage_comp _ (tau_le hW' (hW'k.trans inf_le_left))
  have hkk : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), ⊤ ≤ ((spMap ψ ≫ tau hW') ≫ toFlag M) ⁻¹ᵁ X.F.U k :=
    fun ψ => by
      show ⊤ ≤ (spMap ψ ≫ tau hW') ⁻¹ᵁ (toFlag M ⁻¹ᵁ X.F.U k)
      exact le_preimage_comp _ (tau_le hW' (hW'k.trans inf_le_right))
  have chart : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), ∃ (_ : Algebra c.F K) (Q : FrPt Xo c K),
      X.F.ChartFr k _ (hkk ψ) Q := fun ψ => by
    have hF : ⊤ ≤ ((spMap ψ ≫ tau hW') ≫ toFlag M) ⁻¹ᵁ flagOpen X := fun s _ => by
      have := ho ψ (Set.mem_univ s)
      rw [M.off_eq] at this
      exact this
    obtain ⟨a, h⟩ := exists_chartFr _ hF
    exact ⟨a, h k (hkk ψ)⟩
  have hJ : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), evalPt (spMap ψ ≫ tau hW') W' (hzW ψ) (M.K.jacobian i hW'i g) = ψ (M.K.jacobian i hW'i g) :=
    fun ψ => congrFun (congrArg DFunLike.coe (ev_spMap_tau hW' ψ (hzW ψ))) _
  have hl' : ∀ {K : Type} [Field K] [Algebra c.F K] (ψ : Γ(M.X, W') →+* K) {v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)},
      (∀ b, spMap ((dualMap ψ).comp (e b)) ≫ tau hW' ≫ toFlag M = X.ptY (v b)) → ∀ b, zv ψ b ≫ toFlag M = X.ptY (v b) :=
    fun ψ _ h b => (Category.assoc _ _ _).trans (h b)
  have hne : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), ψ A.det ≠ 0 := fun {K} _ ψ => by
    obtain ⟨_, Q, hQ⟩ := chart ψ
    obtain ⟨v, hv, hl⟩ := e2 K ψ _ Q hQ
    have := GlobalTheory.T.det_derivatives_tangentLift_ne_zero M hKS (spMap ψ ≫ tau hW') (ho ψ) (FlagCover.eq_ptY hQ.lies) hv (hl' ψ hl) i W' hW'i g (hzW ψ)
      (hzvW ψ) (by rw [hJ]; exact (hu.map ψ).ne_zero)
    rwa [hdet] at this
  have hAu : IsUnit A.det := by
    by_contra h
    obtain ⟨m, hm, hdm⟩ := exists_max_ideal_of_mem_nonunits h
    letI := Ideal.Quotient.field m
    exact hne (Ideal.Quotient.mk m) (Ideal.Quotient.eq_zero_iff_mem.2 hdm)
  let a : Γ(M.X, W') := M.K.jacobian i hW'i g * ↑(hAu.unit⁻¹)
  have hinv : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), ψ A.det * ψ ↑(hAu.unit⁻¹) = 1 := fun ψ => by
    rw [← map_mul]
    have : A.det * ↑(hAu.unit⁻¹) = 1 := hAu.mul_val_inv
    rw [this, map_one]
  have rel : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), KSRel M i k (spMap ψ ≫ tau hW') (ψ a) := by
    intro K _ ψ _ P Q t v zv' O hO g' hz hzv hk hQ ht hv hl
    obtain ⟨v0, hv0, hl0⟩ := e2 K ψ hk Q hQ
    have hzO : ∀ b, ⊤ ≤ zv ψ b ⁻¹ᵁ O := fun b => le_preimage_of_dualNumber (TrivSqZeroExt.fstHom K K K).toRingHom _ O
      (by rw [hred]; exact hz)
    have tc := GlobalTheory.T.det_derivatives_borelFrameChange_canonicalWeight M hKS (spMap ψ ≫ tau hW') (ho ψ) t (FlagCover.eq_ptY hQ.lies) ht hv hv0 hl (hl' ψ hl0) O g' hzv hzO
    have jc := GlobalTheory.T.det_derivatives_div_jacobian_independent M (spMap ψ ≫ tau hW') i (fun b => zv ψ (tanOrd Dw b)) (fun b => hred ψ _) O W' hO hW'i g' g hz
      (hzW ψ) (fun b => hzO _) (fun b => hzvW ψ _)
    rw [hJ, hdet] at jc
    rw [tc]
    generalize (Matrix.of fun a b => (evalPt (zv ψ (tanOrd Dw b)) O (hzO _) (g' a)).snd).det = D0 at jc ⊢
    generalize evalPt (spMap ψ ≫ tau hW') O hz (M.K.jacobian i hO g') = J1 at jc ⊢
    generalize ((∏ ix, t ix ^ exOf Dw (kap Dw) 0 ix : Kˣ) : K) = T
    have h1 := hinv ψ
    simp only [a, map_mul]
    generalize ψ ↑(hAu.unit⁻¹) = u at h1 ⊢
    generalize ψ A.det = d at jc h1
    generalize ψ (M.K.jacobian i hW'i g) = J0 at jc ⊢
    calc J0 * u * (T * D0) = T * u * (D0 * J0) := by ring
      _ = T * u * (d * J1) := by rw [jc]
      _ = (d * u) * (T * J1) := by ring
      _ = T * J1 := by rw [h1, one_mul]
  have uniq : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K) (x y : K), KSRel M i k (spMap ψ ≫ tau hW') x →
      KSRel M i k (spMap ψ ≫ tau hW') y → x = y := by
    intro K _ ψ x y hx hy
    obtain ⟨alg, Q, hQ⟩ := chart ψ
    obtain ⟨v0, hv0, hl0⟩ := e2 K ψ _ Q hQ
    have hb := (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c K).1 Q
    have a1 := @hx alg Q Q 1 v0 (zv ψ) W' hW'i g (hzW ψ) (hzvW ψ) _ hQ hb hv0 (hl' ψ hl0)
    have a2 := @hy alg Q Q 1 v0 (zv ψ) W' hW'i g (hzW ψ) (hzvW ψ) _ hQ hb hv0 (hl' ψ hl0)
    rw [hdet] at a1 a2
    exact mul_right_cancel₀ (hne ψ) (a1.trans a2.symm)
  refine ⟨W', a, hpW', hWV, fun L _ z hz => ?_, fun L _ z hz x y hx hy => ?_⟩
  · have e0 : spMap (ev z W' hz) ≫ tau hW' = z := spMap_ev z hW' hz
    have h : KSRel M i k (spMap (ev z W' hz) ≫ tau hW') (ev z W' hz a) := @rel L _ (ev z W' hz)
    rwa [e0] at h
  · have e0 : spMap (ev z W' hz) ≫ tau hW' = z := spMap_ev z hW' hz
    rw [← e0] at hx hy
    exact uniq _ x y hx hy

theorem exists_regular_ksRel : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), GlobalTheory.Published.AbelianDeRham → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (i : M.K.bundle.ι) (k : X.F.J) (W : M.X.Opens), IsAffineOpen W → W ≤ ksOpen M i k → ∃ a : Γ(M.X, W), ∀ (K : Type) [Field K] (z : Sp K ⟶ M.X) (hz : ⊤ ≤ z ⁻¹ᵁ W), KSRel M i k z (GlobalTheory.FlagMod.ev z W hz a) := by
  intro E _ _ _ H Dw l Xo c Y X Z M hP hKS i k W _ hW
  haveI : Smooth M.str := SmoothOfRelativeDimension.smooth (dimFlag Dw) M.str
  haveI : IsReduced M.X := isReduced_of_smooth M.str
  exact glue_field_cover W (fun L _ z x => KSRel M i k z x) (exists_local M hP hKS i k W hW)

end GlobalTheory.CompHS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResolvedModification
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.QuotSetup

theorem geometricallyConnected_of_surjective {X Y Z : Scheme.{0}} (p : X ⟶ Y) (f : Y ⟶ Z)
    [Surjective p] [GeometricallyConnected (p ≫ f)] : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  have : ConnectedSpace ↥(pullback (p ≫ f) x) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  let q := (pullbackRightPullbackFstIso f x p).inv ≫ pullback.snd p (pullback.fst f x)
  have : Surjective q := inferInstance
  exact q.surjective.connectedSpace q.continuous

theorem genericPoint_mem {X : Scheme.{0}} [IsIntegral X] (U : X.Opens) (hU : (U : Set X).Nonempty) :
    genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)

theorem map_genericPoint {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] :
    f (genericPoint X) = genericPoint Y := by
  have := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at this
  exact this.eq (genericPoint_spec Y)

theorem surjective_of_isProjOver {F : Type} [Field F] {Y Z : Scheme.{0}} [IsIntegral Z] (p : Y ⟶ Sp F)
    (pZ : Z ⟶ Sp F) (f : Y ⟶ Z) (hf : f ≫ pZ = p) (hp : IsProjOver p) (hZ : IsProjOver pZ) (y : Y)
    (hy : f y = genericPoint Z) : Surjective f := by
  have h₁ : IsProper (f ≫ pZ) := hf ▸ ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  have : IsProper pZ := ((isProjOver_iff_isProper_and_exists_isAmpleLB pZ).1 hZ).1
  have : IsProper f := IsProper.of_comp f pZ
  have hc : closure {genericPoint Z} ⊆ Set.range f :=
    f.isClosedMap.isClosed_range.closure_subset_iff.2 (by rintro _ rfl; exact ⟨y, hy⟩)
  exact ⟨fun z => hc (by rw [(genericPoint_spec Z).def]; trivial)⟩

end GlobalTheory.QuotSetup

namespace GlobalTheory.QuotSetup

theorem exists_resolved_modification : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [CharZero F] (X X' W V : Scheme.{0}) [IsIntegral X] [IsIntegral X'] [IsIntegral W] (sX : X ⟶ Sp F) (n : ℕ) [SmoothOfRelativeDimension n sX] (φ : X' ⟶ X) (q : X' ⟶ W) (sW : W ⟶ Sp F) (i : V ⟶ X) (ℓ : V ⟶ X'), IsProjOver sX → GeometricallyConnected sX → IsProjOver (φ ≫ sX) → IsProjOver sW → IsFinite q → Surjective q → q ≫ sW = φ ≫ sX → IsOpenImmersion i → IsOpenImmersion ℓ → ℓ ≫ φ = i → ∀ (δ : LB X) (hδ : δ.IsLB) (N : LB W) (hN : N.IsLB), CechPic.pull q (cls N hN) = CechPic.pull φ (cls δ hδ) → ∀ (J : Type) (v : J → (Sp ℂ ⟶ V)), (∀ j j', v j ≫ ℓ ≫ q = v j' ≫ ℓ ≫ q) → (∃ j, ∀ s, (v j ≫ i) s = genericPoint X) → ∃ (W' : Scheme.{0}) (_ : IsIntegral W') (pW : W' ⟶ Sp F) (U : X.Opens) (M : Modif sX U n) (f : M.X ⟶ W') (NW : LB W') (hNW : NW.IsLB), IsIntegral M.X ∧ SmoothOfRelativeDimension n pW ∧ IsProjOver pW ∧ GeometricallyConnected pW ∧ f ≫ pW = M.str ∧ Surjective f ∧ (U : Set X).Nonempty ∧ CechPic.pull f (cls NW hNW) = CechPic.pull M.σ (cls δ hδ) ∧ ∃ z : J → (Sp ℂ ⟶ M.X), (∀ j, ⊤ ≤ z j ⁻¹ᵁ M.opn) ∧ (∀ j, z j ≫ M.σ = v j ≫ i) ∧ (∀ j j', z j ≫ f = z j' ≫ f) ∧ (∀ j s, (z j ≫ f) s = genericPoint W') := by
  intro hP F _ _ X X' W V _ _ _ sX n _ φ q sW i ℓ hsX hgc hφ hsW hqf hqs hw hi hℓ hℓi δ hδ N hN hNδ J v hv hgen
  obtain ⟨j₀, hj₀⟩ := hgen
  obtain ⟨o₀⟩ : Nonempty (Sp ℂ) := inferInstance
  haveI : Nonempty V := ⟨v j₀ o₀⟩
  haveI : IsIntegral V := isIntegral_of_isOpenImmersion i
  haveI : Nonempty X := ⟨i (v j₀ o₀)⟩
  have hpX : IsProper sX := ((isProjOver_iff_isProper_and_exists_isAmpleLB sX).1 hsX).1
  have hpX' : IsProper (φ ≫ sX) := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hφ).1
  have hpW : IsProper sW := ((isProjOver_iff_isProper_and_exists_isAmpleLB sW).1 hsW).1

  have hWgen : ∀ j o, (v j ≫ ℓ ≫ q) o = genericPoint W := fun j o => by
    rw [hv j j₀]
    have h₁ : v j₀ o = genericPoint V :=
      i.isOpenEmbedding.injective ((hj₀ o).trans (genericPoint_eq_of_isOpenImmersion i).symm)
    simp only [Scheme.Hom.comp_apply]
    rw [h₁, genericPoint_eq_of_isOpenImmersion ℓ, map_genericPoint q]

  have hdW : topologicalKrullDim W = n := by
    have hdX : topologicalKrullDim X = n := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth sX n inferInstance
    have hdV := GlobalTheory.T.topologicalKrullDim_eq_of_openImmersion_integral_scheme F X V sX i
    have hdV' := GlobalTheory.T.topologicalKrullDim_eq_of_openImmersion_integral_scheme F X' V (φ ≫ sX) ℓ
    have h₁ := PosBaseChange.dim_le_of_isClosedMap q.isClosedMap q.surjective
    have h₂ := PosBaseChange.dim_le_of_isDiscrete q.continuous q.isDiscrete_preimage_singleton
    rw [← hdX, ← hdV, hdV']
    exact le_antisymm h₁ h₂

  obtain ⟨W', s, UW, hW', hsm, hpj, hUW, hiso⟩ := GlobalTheory.T.weak_resolution_of_principalisation hP F W sW n hsW hdW
  haveI := hW'
  haveI := hiso
  have hηUW : genericPoint W ∈ UW := genericPoint_mem UW hUW

  let O : V.Opens := (ℓ ≫ q) ⁻¹ᵁ UW
  have hvO : ∀ j o, v j o ∈ O := fun j o => by
    show (ℓ ≫ q) (v j o) ∈ UW
    rw [← Scheme.Hom.comp_apply, hWgen j o]
    exact hηUW
  let U : X.Opens := i ''ᵁ O
  have hUi : Set.range U.ι ⊆ Set.range i := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  let e : U.toScheme ⟶ V := IsOpenImmersion.lift i U.ι hUi
  have he : e ≫ i = U.ι := IsOpenImmersion.lift_fac _ _ _
  have hc : Set.range (e ≫ ℓ ≫ q) ⊆ Set.range UW.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have hx : i (e x) ∈ U := by rw [← Scheme.Hom.comp_apply, he]; exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rw [i.isOpenEmbedding.injective hyx] at hy
    exact hy
  let c : U.toScheme ⟶ UW.toScheme := IsOpenImmersion.lift UW.ι (e ≫ ℓ ≫ q) hc
  have hcf : c ≫ UW.ι = e ≫ ℓ ≫ q := IsOpenImmersion.lift_fac _ _ _
  let b : UW.toScheme ⟶ W' := inv (s ∣_ UW) ≫ (s ⁻¹ᵁ UW).ι
  have hb : b ≫ s = UW.ι := by simp [b, ← morphismRestrict_ι]
  let r₀ : U.toScheme ⟶ pullback q s :=
    pullback.lift (e ≫ ℓ) (c ≫ b) (by rw [Category.assoc, Category.assoc, hb, hcf])
  have hUne : (U : Set X).Nonempty := ⟨i (v j₀ o₀), v j₀ o₀, hvO j₀ o₀, rfl⟩
  have ht : IsProjOver (pullback.snd q s ≫ s ≫ sW) := isProjOver_comp_of_isFinite _ hpj
  have hr₀ : r₀ ≫ pullback.snd q s ≫ s ≫ sW = U.ι ≫ sX := by
    simp only [r₀, pullback.lift_snd_assoc, Category.assoc]
    rw [reassoc_of% hb, reassoc_of% hcf, hw, reassoc_of% hℓi, reassoc_of% he]
  obtain ⟨M, r, hMi, hrt, hrM⟩ :=
    GlobalTheory.T.exists_modification_extending_map_from_open hP F X (pullback q s) sX n (pullback.snd q s ≫ s ≫ sW) U r₀ inferInstance hsX ht hUne hr₀
  haveI := hMi
  have hsep : IsSeparated sX := inferInstance
  haveI : IsDominant M.opn.ι := ⟨show Dense (Set.range M.opn.ι) by rw [Scheme.Opens.range_ι]; exact M.dense⟩
  have hσ : r ≫ pullback.fst q s ≫ φ = M.σ := by
    refine ext_of_isDominant_of_isSeparated sX ?_ M.opn.ι ?_
    · simp only [Category.assoc]
      rw [← hw, pullback.condition_assoc]
      exact hrt
    · rw [reassoc_of% hrM]
      simp only [r₀, pullback.lift_fst_assoc, Category.assoc]
      rw [hℓi, he, morphismRestrict_ι]
  let f : M.X ⟶ W' := r ≫ pullback.snd q s
  have hfs : f ≫ s = (r ≫ pullback.fst q s) ≫ q := by
    simp only [f, Category.assoc, pullback.condition]
  have hfp : f ≫ s ≫ sW = M.str := by
    simp only [f, Category.assoc]; exact hrt

  have hvU : ∀ j, ⊤ ≤ (v j ≫ i) ⁻¹ᵁ U := fun j o _ => by
    show (v j ≫ i) o ∈ U
    rw [Scheme.Hom.comp_apply]
    exact ⟨v j o, hvO j o, rfl⟩
  choose z hz using fun j => (M.existsUnique_lift (v j ≫ i) (hvU j)).exists
  have hzU : ∀ j, ⊤ ≤ z j ⁻¹ᵁ M.opn := fun j => by
    show ⊤ ≤ z j ⁻¹ᵁ (M.σ ⁻¹ᵁ U)
    rw [← Scheme.Hom.comp_preimage, hz j]
    exact hvU j
  have key : ∀ j, ∃ d : Sp ℂ ⟶ UW.toScheme, d ≫ UW.ι = v j ≫ ℓ ≫ q ∧ z j ≫ f = d ≫ b := fun j => by
    have hr : Set.range (z j) ⊆ Set.range M.opn.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨o, rfl⟩
      exact hzU j (Set.mem_univ o)
    let w := IsOpenImmersion.lift M.opn.ι (z j) hr
    have hw' : w ≫ M.opn.ι = z j := IsOpenImmersion.lift_fac _ _ _
    have hwe : w ≫ (M.σ ∣_ U) ≫ e = v j := by
      rw [← cancel_mono i, Category.assoc, Category.assoc, he, morphismRestrict_ι, reassoc_of% hw', hz j]
    refine ⟨w ≫ (M.σ ∣_ U) ≫ c, ?_, ?_⟩
    · rw [Category.assoc, Category.assoc, hcf, ← reassoc_of% hwe]
    · simp only [f, ← hw', Category.assoc]
      rw [reassoc_of% hrM]
      simp only [r₀, pullback.lift_snd, Category.assoc]
  choose d hd hzd using key
  haveI : Nonempty UW.toScheme := ⟨⟨_, hηUW⟩⟩
  haveI : IsIntegral UW.toScheme := isIntegral_of_isOpenImmersion UW.ι
  have hgen' : ∀ j o, (z j ≫ f) o = genericPoint W' := fun j o => by
    have h₁ : d j o = genericPoint UW.toScheme := by
      apply UW.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hd j, hWgen j o, genericPoint_eq_of_isOpenImmersion UW.ι]
    rw [hzd j, Scheme.Hom.comp_apply, h₁]
    exact genericPoint_eq_of_isOpenImmersion b
  have hfsurj : Surjective f :=
    surjective_of_isProjOver M.str (s ≫ sW) f hfp M.proj hpj (z j₀ o₀) (by rw [← Scheme.Hom.comp_apply]; exact hgen' j₀ o₀)
  have hgcM : GeometricallyConnected M.str := GlobalTheory.T.geometricallyConnected_smoothProjModification_offOpen F X sX n U M hUne
  have hgcW : GeometricallyConnected (s ≫ sW) := by
    rw [← hfp] at hgcM
    exact geometricallyConnected_of_surjective f (s ≫ sW)
  refine ⟨W', hW', s ≫ sW, U, M, f, N.pull s, LB.isLB_pull hN s, hMi, hsm, hpj, hgcW, hfp, hfsurj, hUne, ?_,
    z, hzU, hz, fun j j' => ?_, hgen'⟩
  · rw [cls_pull hN s, ← pull_comp, hfs, pull_comp, hNδ, ← pull_comp, Category.assoc, hσ]
  · rw [hzd j, hzd j']
    congr 1
    rw [← cancel_mono UW.ι, hd j, hd j', hv j j']

end GlobalTheory.QuotSetup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigIsoOfIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigLBIso

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem exists_rig_iso_of_iso : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L₁ L₂ : RigLB G), LBIso L₁.L L₂.L → ∃ wL : LB.Iso L₁.L L₂.L, wL.IsGen ∧ LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L₁.rig L₂.rig := by
  rintro S G _ _ L₁ L₂ ⟨w, hw⟩
  have hw₀ : PGen (isoPullId w (F := 𝟙 G.left) rfl) := isoPullId_pgen hw rfl
  obtain ⟨c, hc⟩ := GlobalTheory.Unif.RigidifyIso.exists_ratio (K := PUnit) (φ' := fun _ => eSec G)
    (φ := fun _ => eSec G) (ε := fun _ => 1) hw₀ L₂.isLB L₁.isLB (𝟙 _)
    (fun _ => by rw [Category.comp_id, Category.id_comp]) L₁.rig L₁.rigGen L₂.rig L₂.rigGen
  let π : G.left ⟶ (𝟙_ (Over S)).left := G.hom
  have hs : eSec G ≫ π = 𝟙 _ := Over.w η[G]
  let wL : LB.Iso L₁.L L₂.L := ⟨fun i => res (le_top : _ ≤ π ⁻¹ᵁ ⊤) (pullU π ⊤ c) * w.s i⟩
  have hv : ∀ (Y : Scheme.{0}) (f : Y ⟶ G.left) (y : Y) (j : L₂.L.ι) (k : L₁.L.ι), f y ∈ L₂.L.U j →
      f y ∈ L₁.L.U k → gv wL f y j k = gm (f ≫ π) y ⊤ c * gv w f y j k := by
    intro Y f y j k hj hk
    have hz : f y ∈ L₂.L.U j ⊓ L₁.L.U k := ⟨hj, hk⟩
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res f y _ hz _).trans (gm_pull f π y ⊤ trivial c)) rfl)
  refine ⟨wL, ?_, ?_⟩
  · rintro p q
    apply unit_ext
    intro x hx
    have h1 : (𝟙 G.left) x ∈ L₂.L.U p.1 := hx.1.1
    have h2 : (𝟙 G.left) x ∈ L₁.L.U p.2 := hx.1.2
    have h3 : (𝟙 G.left) x ∈ L₂.L.U q.1 := hx.2.1
    have h4 : (𝟙 G.left) x ∈ L₁.L.U q.2 := hx.2.2
    have eL : gm (𝟙 G.left) x _ (res (inf_le_left : (L₂.L.div L₁.L).U p ⊓ (L₂.L.div L₁.L).U q ≤ _) (wL.s p)) =
        gv wL (𝟙 G.left) x p.1 p.2 := gm_res (𝟙 G.left) x _ hx _
    have eR : gm (𝟙 G.left) x _ ((L₂.L.div L₁.L).g p q *
        res (inf_le_right : (L₂.L.div L₁.L).U p ⊓ (L₂.L.div L₁.L).U q ≤ _) (wL.s q)) =
        gm (𝟙 G.left) x _ (L₂.L.g p.1 q.1) * (gm (𝟙 G.left) x _ (L₁.L.g p.2 q.2))⁻¹ * gv wL (𝟙 G.left) x q.1 q.2 :=
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div L₁.L L₂.L (𝟙 G.left) x p q hx) (gm_res (𝟙 G.left) x _ hx _))
    rw [eL, eR, hv _ _ x _ _ h1 h2, hv _ _ x _ _ h3 h4, gm_isGen hw (𝟙 G.left) x p.1 q.1 p.2 q.2 h1 h3 h2 h4]
    exact mul_left_comm _ _ _
  · rintro ⟨P, Q⟩
    apply unit_ext
    intro x hx
    have hj : (eSec G) x ∈ L₂.L.U (P PUnit.unit) := Set.mem_iInter.1 hx.1 PUnit.unit
    have hk : (eSec G) x ∈ L₁.L.U (Q PUnit.unit) := Set.mem_iInter.1 hx.2 PUnit.unit
    have hj' : (𝟙 _ ≫ eSec G) x ∈ L₂.L.U (P PUnit.unit) := Set.mem_iInter.1 hx.1 PUnit.unit
    have hk' : (𝟙 _ ≫ eSec G) x ∈ L₁.L.U (Q PUnit.unit) := Set.mem_iInter.1 hx.2 PUnit.unit
    have hc' := hc _ (𝟙 _) x P Q (by simp only [Category.comp_id]; exact hx.1) hx.2
    have ep : ReciprocityTheory.ChartRestriction.G.Geo.Tor.pw (isoPullId w (F := 𝟙 G.left) rfl) (K := PUnit) (fun _ => eSec G) (fun _ => 1)
        (𝟙 _) x P Q = gv w (𝟙 _ ≫ eSec G) x (P PUnit.unit) (Q PUnit.unit) := by
      show ∏ k : PUnit, _ = _
      rw [Fintype.prod_unique, zpow_one]
      exact gw_isoPullId w rfl _ x _ _ hj' hk'
    rw [Category.comp_id, ep] at hc'
    have eL : gm (𝟙 _) x _ (res (inf_le_left : LB.wchart L₂.L (fun _ => eSec G) P ⊓ LB.wchart L₁.L (fun _ => eSec G) Q ≤ _)
        (L₂.rig.s P)) = gm (𝟙 _) x _ (L₂.rig.s P) := gm_res (𝟙 _) x _ hx _
    have eR : gm (𝟙 _) x _ (@id (Γ((𝟙_ (Over S)).left, LB.wchart L₂.L (fun _ => eSec G) P ⊓ LB.wchart L₁.L (fun _ => eSec G) Q)ˣ) ((LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)).s (P, Q)) *
        res (inf_le_right : LB.wchart L₂.L (fun _ => eSec G) P ⊓ LB.wchart L₁.L (fun _ => eSec G) Q ≤ _) (L₁.rig.s Q)) =
        gv wL (𝟙 _ ≫ eSec G) x (P PUnit.unit) (Q PUnit.unit) * gm (𝟙 _) x _ (L₁.rig.s Q) := by
      refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gm_res (𝟙 _) x _ hx _))
      show gm (𝟙 _) x _ (∏ _k : PUnit, (res _ (pullU (eSec G) _ (wL.s (P PUnit.unit, Q PUnit.unit)))) ^ (1 : ℤ)) = _
      rw [Fintype.prod_unique, zpow_one]
      exact (gm_res (𝟙 _) x _ hx _).trans (gm_pull (𝟙 _) (eSec G) x (L₂.L.U (P PUnit.unit) ⊓ L₁.L.U (Q PUnit.unit)) ⟨hj, hk⟩ _)
    refine eL.trans (hc'.trans (Eq.trans ?_ eR.symm))
    rw [hv _ _ x _ _ hj' hk', Category.assoc, hs, Category.comp_id]
    exact (mul_assoc _ _ _).symm

end GlobalTheory.RigLBIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfNaturalOnAlgebraPointsOfCoverStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_of_natural_on_algebraPoints_of_cover : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) (W : J → X.Opens) (U : X.Opens), (∀ j, W j ≤ U) → U ≤ ⨆ j, W j → ∀ F : PtFn s, (∀ j, IsNat (W j) F) → ∃ f : Γ(X, U), ∀ (j : J) (P : Pt s), P.In (W j) → F P = valR P.x U f := by
  first | exact @GlobalTheory.CechKS.exists_sec_of_isNat | exact GlobalTheory.CechKS.exists_sec_of_isNat | (intros; apply GlobalTheory.CechKS.exists_sec_of_isNat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPowerNonvanishingStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
open GlobalTheory.AbLaw GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_power_nonvanishing : ∀ {Y : Scheme.{0}} {D : LB Y} {J : Type} (s : J → LB.Sec D) (i : J) {x : Y}, x ∈ Out.nonzeroLocus (s i) → ∀ u : ℕ, ∃ σ : LB.Sec (pw D u), x ∈ Out.nonzeroLocus σ := by
  first | exact @GlobalTheory.PowSecNonzero.exists_pw_sec_nonzero | exact GlobalTheory.PowSecNonzero.exists_pw_sec_nonzero | (intros; apply GlobalTheory.PowSecNonzero.exists_pw_sec_nonzero <;> assumption)
end

