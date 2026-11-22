import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2267
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2266
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2278
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationExtendLocalizationAtPrime
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem derivation_extend_localization_atPrime (F A R : Type) [CommRing F] [CommRing A] [CommRing R]
    [Algebra F A] [Algebra A R] [Algebra F R] [IsScalarTower F A R] (P : Ideal A) [P.IsPrime]
    [IsLocalization.AtPrime R P] (D : Derivation F A R) :
    ∃ D' : Derivation F R R, ∀ a, D' (algebraMap A R a) = D a := by
  haveI : Algebra.FormallyEtale A R := Algebra.FormallyEtale.of_isLocalization P.primeCompl
  have hb := KaehlerDifferential.isBaseChange_of_formallyEtale F A R
  refine ⟨(hb.lift D.liftKaehlerDifferential).compDer (KaehlerDifferential.D F R), fun a => ?_⟩
  show hb.lift D.liftKaehlerDifferential (KaehlerDifferential.D F R (algebraMap A R a)) = D a
  rw [← KaehlerDifferential.map_D F F A R, hb.lift_eq, Derivation.liftKaehlerDifferential_comp_D]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeBasePullbackEqZeroAlongVerticalDeforma
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPole

theorem snd_ev_toBase_of_isVert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.Opens) (W : (Y₀ TF.X Z).Opens) (hW : W ≤ toBase TF Z ⁻¹ᵁ U) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (N' : GlobalTheory.FlagTan.FIx Dw → K) (w : FrPt Xo c (DualNumber K)) (zw : Sp (DualNumber K) ⟶ Y₀ TF.X Z) (hzw : ⊤ ≤ zw ⁻¹ᵁ W), IsVert P N' w → zw ≫ inc₀ TF.X Z = TF.X.ptY w → ∀ r, (ev zw W hzw (((toBase TF Z).appLE U W hW).hom r)).snd = 0 := by
  intro E _ _ _ H Dw l Xo c TF Z U W hW K _ _ P N' w zw hzw hv hz r
  have hx : w.x = spMap (GlobalTheory.FlagTan.cst c K).toRingHom ≫ P.x := (GlobalTheory.FlagTan.exists_isVert_iff.1 ⟨N', hv⟩).2
  have hfr : frX w = spMap (GlobalTheory.FlagTan.cst c K).toRingHom ≫ frX P :=
    (GlobalTheory.FlagMod.eq_frX w (by rw [Category.assoc, GlobalTheory.FlagMod.frX_fst, hx])
      (by rw [Category.assoc, GlobalTheory.FlagMod.frX_snd, spMap_comp']
          exact congrArg spMap (GlobalTheory.FlagTan.cst c K).comp_algebraMap)).symm
  have hb : zw ≫ toBase TF Z = spMap (GlobalTheory.FlagTan.cst c K).toRingHom ≫ (frX P ≫ TF.Y.j) := by
    show zw ≫ (inc₀ TF.X Z ≫ TF.X.π) = _
    rw [← Category.assoc, hz, (TF.X.lies_ptY w).1, hfr, Category.assoc]
  have h1 : ⊤ ≤ (zw ≫ toBase TF Z) ⁻¹ᵁ U := fun s _ => hW (hzw (Set.mem_univ s))
  have h2 : ⊤ ≤ (spMap (GlobalTheory.FlagTan.cst c K).toRingHom ≫ (frX P ≫ TF.Y.j)) ⁻¹ᵁ U := hb ▸ h1
  have hK : ∀ a b : PrimeSpectrum K, a = b := fun a b => by
    ext x
    rw [(Ideal.eq_bot_or_top a.asIdeal).resolve_right a.2.ne_top,
      (Ideal.eq_bot_or_top b.asIdeal).resolve_right b.2.ne_top]
  have h3 : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U := fun s _ => by
    have hp : (spMap (GlobalTheory.FlagTan.cst c K).toRingHom)
        ((spMap (TrivSqZeroExt.fstHom c.F K K).toRingHom) (IsLocalRing.closedPoint K)) = s := hK _ _
    have h₁ := h2 (Set.mem_univ ((spMap (TrivSqZeroExt.fstHom c.F K K).toRingHom) (IsLocalRing.closedPoint K)))
    exact hp ▸ h₁
  rw [GlobalTheory.FlagMod.ev_appLE zw (toBase TF Z) hW hzw h1, GlobalTheory.FlagMod.ev_congr hb U h1 h2,
    GlobalTheory.FlagMod.ev_spMap _ _ U h3 h2]
  simp

end GlobalTheory.LogPole
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescCocycle
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LBDescent

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

abbrev Triple : Scheme.{0} := pullback (pullback.snd f f) (pullback.fst f f)

def pr13 : Triple f ⟶ pullback f f :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst f f) (pullback.snd _ _ ≫ pullback.snd f f) (by
    calc (pullback.fst _ _ ≫ pullback.fst f f) ≫ f = pullback.fst (pullback.snd f f) (pullback.fst f f) ≫
          pullback.snd f f ≫ f := by rw [Category.assoc, pullback.condition]
      _ = pullback.snd (pullback.snd f f) (pullback.fst f f) ≫ pullback.fst f f ≫ f := pullback.condition_assoc _
      _ = (pullback.snd _ _ ≫ pullback.snd f f) ≫ f := by rw [pullback.condition, Category.assoc])

def chart (L : LB X) (i j : L.ι) : (pullback f f).Opens :=
  pullback.fst f f ⁻¹ᵁ L.U i ⊓ pullback.snd f f ⁻¹ᵁ L.U j

def DescCompat (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ) : Prop :=
  ∀ (z : ↥(pullback f f)) (i i' j j' : L.ι), pullback.fst f f z ∈ L.U i → pullback.fst f f z ∈ L.U i' →
    pullback.snd f f z ∈ L.U j → pullback.snd f f z ∈ L.U j' →
    gm (𝟙 _) z _ (φ i' j') =
      gm (pullback.fst f f) z _ (L.g i i') * gm (𝟙 _) z _ (φ i j) * gm (pullback.snd f f) z _ (L.g j' j)

def DescCocycle (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ) : Prop :=
  ∀ (w : ↥(Triple f)) (i j k : L.ι), pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w) ∈ L.U i →
    pullback.snd f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w) ∈ L.U j → pullback.snd f f (pullback.snd (pullback.snd f f) (pullback.fst f f) w) ∈ L.U k →
    gm (pullback.fst (pullback.snd f f) (pullback.fst f f)) w _ (φ i j) *
      gm (pullback.snd (pullback.snd f f) (pullback.fst f f)) w _ (φ j k) = gm (pr13 f) w _ (φ i k)

end GlobalTheory.LBDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentMapContinuousSurjective
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mean4O.Cover

variable {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y)

theorem residueDegree_pos_at (w : V.G) : 0 < V.π.residueDegree w := by
  let := (V.π.residueFieldMap w).hom.toAlgebra
  have : Module.Finite (Y.X.residueField (V.π w)) (V.G.residueField w) :=
    residueFieldMap_finite_of_locallyQuasiFinite V.π _
  exact Module.finrank_pos

theorem exists_lift_cx (y : Sp ℂ ⟶ Y.X) : ∃ w : Sp ℂ ⟶ V.G, w ≫ V.π = y := by
  obtain ⟨x, hx⟩ := V.π.surjective (below y)
  have hp : 0 < Nat.card {z : Sp ℂ ⟶ V.G // below z = x ∧ z ≫ V.π = y} :=
    (CoverHt.card_lifts V.π x y hx.symm).symm ▸ residueDegree_pos_at V x
  obtain ⟨⟨z, -, hz⟩⟩ := (Nat.card_pos_iff.1 hp).1
  exact ⟨z, hz⟩

theorem isDown_continuous_surjective : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (e : ℕ)
    (M : Man e) (I : ManIs M Y) (ε : (𝓞 F →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts V.p σ → M.X (ε σ)),
    V.IsDown I ε π → ∀ σ, Continuous (π σ) ∧ Function.Surjective (π σ) := by
  intro F _ _ Y V e M I ε π hD σ
  obtain ⟨hε, hw⟩ := hD σ
  have hs : spMap σ = spMap (I.ε (ε σ)) ≫ spMap (algebraMap (𝓞 F) F) :=
    (congrArg spMap hε.symm).trans (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _))
  let L : CxPts V.p σ → (Sp ℂ ⟶ V.G) := fun z => V.pb.lift z.1 (spMap (I.ε (ε σ))) (z.2.trans hs)
  have key (z : CxPts V.p σ) : (I.pt _ (π σ z)).1 = L z ≫ V.π := by
    obtain ⟨w, hw1, hw2⟩ := hw z
    have h : w = L z := V.pb.hom_ext (by rw [hw1, V.pb.lift_fst])
      (by rw [V.pb.lift_snd, ← Category.assoc, hw2]; exact (I.pt _ (π σ z)).2)
    rw [← hw2, h]
  have hL : Continuous L := by
    rw [(Points.isEmbedding_of_isPullback (C := ℂ) V.pb).continuous_iff]
    have h : ((fun z : Sp ℂ ⟶ V.G => (z ≫ V.j, z ≫ (V.π ≫ Y.str))) ∘ L) =
        fun z => (z.1, spMap (I.ε (ε σ))) :=
      funext fun z => Prod.ext (V.pb.lift_fst _ _ _) (V.pb.lift_snd _ _ _)
    rw [h]
    exact continuous_subtype_val.prodMk continuous_const
  refine ⟨?_, fun y => ?_⟩
  · rw [← (I.pt (ε σ)).comp_continuous_iff]
    refine continuous_induced_rng.2 ?_
    exact ((Points.continuous_comp V.π).comp hL).congr fun z => (key z).symm
  · obtain ⟨w, hw'⟩ := exists_lift_cx V (I.pt _ y).1
    have hwτ : w ≫ V.π ≫ Y.str = spMap (I.ε (ε σ)) := by
      rw [← Category.assoc, hw']; exact (I.pt _ y).2
    have hz : (w ≫ V.j) ≫ V.p = spMap σ := by
      rw [Category.assoc, V.pb.w, ← Category.assoc, hwτ, hs]
    refine ⟨⟨w ≫ V.j, hz⟩, (I.pt _).injective (Subtype.ext ?_)⟩
    rw [key]
    have h : L ⟨w ≫ V.j, hz⟩ = w := V.pb.hom_ext (V.pb.lift_fst _ _ _) ((V.pb.lift_snd _ _ _).trans hwτ.symm)
    rw [h, hw']

end GlobalTheory.Mean4O.Cover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBigCellCoordinateJacobianVerticalChangesEqOne
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.LogPole.VertDet

theorem det_eq_one_of_key {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R] (A : Matrix ι ι R) (k : ι → ℕ)
    (h : ∀ a b, a ≠ b → k a ≤ k b → A a b = 0) (hd : ∀ a, A a a = 1) : A.det = 1 := by
  rw [Matrix.det_apply, Finset.sum_eq_single 1]
  · simp [hd]
  · intro s _ hs
    obtain ⟨i, hi, hk⟩ : ∃ i, s i ≠ i ∧ k (s i) ≤ k i := by
      by_contra hc
      push_neg at hc
      obtain ⟨i₀, hi₀⟩ : ∃ i, s i ≠ i := by
        by_contra h0
        push_neg at h0
        exact hs (Equiv.ext h0)
      have hlt : ∑ i, k i < ∑ i, k (s i) := by
        refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i₀, Finset.mem_univ _, hc i₀ hi₀⟩
        by_cases e : s i = i
        · rw [e]
        · exact (hc i e).le
      rw [Equiv.sum_comp s k] at hlt
      exact lt_irrefl _ hlt
    rw [Finset.prod_eq_zero (f := fun j => A (s j) j) (Finset.mem_univ i) (h _ _ hi hk), smul_zero]
  · intro h1
    exact absurd (Finset.mem_univ _) h1

theorem snd_unip_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {K : Type} [Field K] (N : GlobalTheory.FlagTan.FIx Dw → K) (σ : E →+* ℂ)
    (M : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K) (p q : Fin (Dw.mult σ)) :
    ((GlobalTheory.FlagTan.unip K N σ * M.map (fun r => (TrivSqZeroExt.inl r : DualNumber K))) p q).snd
      = ∑ r, N (some ⟨σ, p, r⟩) * M r q := by
  rw [Matrix.mul_apply, TrivSqZeroExt.snd_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp [GlobalTheory.FlagTan.unip, TrivSqZeroExt.snd_mul, mul_comm]

theorem det_vert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (K : Type) [Field K] (M : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K), (∀ σ i j, j < i → M σ i j = 0) → (∀ σ i, M σ i i = 1) → (Matrix.of fun a b : VIx Dw => ((GlobalTheory.FlagTan.unip K (Pi.single b.toF (1 : K)) a.1 * (M a.1).map (fun r => (TrivSqZeroExt.inl r : DualNumber K))) a.2.1.1 a.2.1.2).snd).det = 1 := by
  intro E _ _ _ H Dw K _ M hM hM1
  refine det_eq_one_of_key _ (fun a => (a.2.1.2 : ℕ)) ?_ ?_
  · rintro ⟨σ, ⟨p, q⟩, hpq⟩ ⟨τ, ⟨i, j⟩, hij⟩ hne hk
    rw [Matrix.of_apply, snd_unip_mul]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases e : (some ⟨σ, p, r⟩ : GlobalTheory.FlagTan.FIx Dw) = GlobalTheory.FlagTan.VIx.toF ⟨τ, ⟨(i, j), hij⟩⟩
    · obtain ⟨rfl, e'⟩ := Sigma.mk.inj_iff.1 (Option.some.inj e)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq e')
      have hlt : q < r := lt_of_le_of_ne hk (by rintro rfl; exact hne rfl)
      rw [hM _ _ _ hlt, mul_zero]
    · rw [Pi.single_eq_of_ne e, zero_mul]
  · rintro ⟨σ, ⟨p, q⟩, hpq⟩
    rw [Matrix.of_apply, snd_unip_mul, Finset.sum_eq_single q]
    · rw [hM1, mul_one]
      exact Pi.single_eq_same _ _
    · intro r _ hr
      rw [Pi.single_eq_of_ne, zero_mul]
      intro e
      obtain ⟨-, e'⟩ := Sigma.mk.inj_iff.1 (Option.some.inj e)
      exact hr (Prod.mk.inj (eq_of_heq e')).2
    · intro h1
      exact absurd (Finset.mem_univ _) h1

end GlobalTheory.LogPole.VertDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFlagTangentConjugateMatrixChangeEqOne
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.KSChgDet

theorem ksChg_single_eq_blockDiagonal' {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} (K : Type) [Field K] (Φ : Finset (E →+* ℂ))
    (g : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K) (k l : HIx Dw Φ) :
    FlagTan.ksChg Φ g ((Pi.single l 1 : HIx Dw Φ → K)) k =
      Matrix.blockDiagonal' (fun τ : Φ => Matrix.kroneckerMap (· * ·)
        (g (conjEmb τ.1)).transpose (g τ.1).transpose) k l := by
  obtain ⟨τ, a, b⟩ := k
  obtain ⟨τ', a', b'⟩ := l
  rw [FlagTan.ksChg_apply]
  by_cases h : τ = τ'
  · subst h
    rw [Matrix.blockDiagonal'_apply_eq]
    simp [Matrix.kroneckerMap_apply, Pi.single_apply, Sigma.mk.inj_iff, ite_and]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
    simp [Pi.single_apply, Sigma.mk.inj_iff, h]

theorem det_ksChg_eq_one : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (K : Type) [Field K] (g : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K),
    (∀ σ, (g σ).det = 1) → ∀ (o : Fin Dw.dim ≃ HIx Dw (psiSet H)),
    (Matrix.of fun i j => FlagTan.ksChg (psiSet H) g ((Pi.single (o j) 1 : HIx Dw (psiSet H) → K)) (o i)).det = 1 := by
  intro E _ _ _ H Dw K _ g hg o
  have hM : (Matrix.of fun i j => FlagTan.ksChg (psiSet H) g ((Pi.single (o j) 1 : HIx Dw (psiSet H) → K)) (o i)) =
      (Matrix.blockDiagonal' (fun τ : psiSet H => Matrix.kroneckerMap (· * ·)
        (g (conjEmb τ.1)).transpose (g τ.1).transpose)).submatrix o o := by
    ext i j
    exact ksChg_single_eq_blockDiagonal' K (psiSet H) g (o i) (o j)
  rw [hM, Matrix.det_submatrix_equiv_self, GlobalTheory.Div.BlockChangeDet.det_blockDiagonal'_eq_prod]
  simp [Matrix.det_kronecker, Matrix.det_transpose, hg]

end GlobalTheory.KSChgDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFrameChangeBalancedTensorsCmType
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
namespace GlobalTheory.LogKSDiv.DetChange

open GlobalTheory.LogKSDiv
open Classical

theorem sandwich {ι κ K : Type} [Fintype ι] [DecidableEq ι] [CommRing K] (B : Matrix ι κ K) (a b : ι) (x y : κ) :
    (Matrix.transpose B * Matrix.of (fun u v => (if u = a ∧ v = b then (1 : K) else 0) + (if u = b ∧ v = a then 1 else 0)) * B) x y =
      B a x * B b y + B b x * B a y := by
  simp [Matrix.mul_apply, add_mul, mul_add, Finset.sum_add_distrib, ite_and, Finset.sum_mul, Finset.mul_sum]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem hostRoot_conj_eq_neg_and_ne_zero (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : starRingEnd ℂ H.rt0 = -H.rt0 ∧ H.rt0 ≠ 0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h := H.sqrt_neg_disc_sq
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_two] at hre him
  have hre0 : H.rt0.re = 0 := by
    by_contra hne
    have : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [this] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  refine ⟨Complex.ext (by simp [hre0]) (by simp), ?_⟩
  intro h0
  rw [h0] at hre
  simp at hre
  exact H.d_prime.ne_zero hre

theorem emb_rt_cases (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) :
    τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
  apply sq_eq_sq_iff_eq_or_eq_neg.1
  rw [H.sqrt_neg_disc_sq, ← map_pow]
  have : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  rw [this]; simp

theorem conj_off (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) (h : τ (H.rt : E) = H.rt0) :
    ((starRingEnd ℂ).comp τ) (H.rt : E) ≠ H.rt0 := by
  obtain ⟨h1, h2⟩ := hostRoot_conj_eq_neg_and_ne_zero H
  rw [RingHom.comp_apply, h, h1]
  intro h3
  exact h2 (by linear_combination (-1/2 : ℂ) * h3)

theorem conj_on (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) (h : τ (H.rt : E) ≠ H.rt0) :
    ((starRingEnd ℂ).comp τ) (H.rt : E) = H.rt0 := by
  rcases emb_rt_cases H τ with h' | h'
  · exact absurd h' h
  · rw [RingHom.comp_apply, h', map_neg, (hostRoot_conj_eq_neg_and_ne_zero H).1, neg_neg]

theorem conj_conj_emb (τ : E →+* ℂ) : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp τ) = τ := by
  ext x; simp

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {K : Type} [Field K]

theorem flatFrame_eq (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) {n n' : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
    (a b : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) :
    flatFrame A e e' (e a) (e' b) = Matrix.blockDiagonal' A a b := by
  simp [flatFrame]

def kronBlocks (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) :
    Matrix (PairIx H Dw) (PairIx H Dw) K :=
  Matrix.blockDiagonal' fun τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} =>
    Matrix.kroneckerMap (· * ·) (A τ.1).transpose (A ((starRingEnd ℂ).comp τ.1)).transpose

theorem lhs_entry (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) {n n' : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
    (P Q : PairIx H Dw) :
    (Matrix.transpose (flatFrame A e e') * symPair (R := K) e P * flatFrame A e e')
      (e' ⟨Q.1.1, Q.2.1⟩) (e' ⟨(starRingEnd ℂ).comp Q.1.1, Q.2.2⟩) = kronBlocks A Q P := by
  unfold symPair
  rw [sandwich, flatFrame_eq, flatFrame_eq, flatFrame_eq, flatFrame_eq]
  obtain ⟨⟨τ, hτ⟩, i, k⟩ := P
  obtain ⟨⟨σ, hσ⟩, i', k'⟩ := Q
  have hne : (starRingEnd ℂ).comp τ ≠ σ := fun h => conj_off H τ hτ (h ▸ hσ)
  dsimp only
  rw [Matrix.blockDiagonal'_apply_ne A _ _ hne, zero_mul, add_zero]
  by_cases h : τ = σ
  · subst h
    simp [kronBlocks, Matrix.blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply]
  · have h' : (⟨σ, hσ⟩ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}) ≠ ⟨τ, hτ⟩ := fun h2 => h (congrArg Subtype.val h2).symm
    simp [kronBlocks, Matrix.blockDiagonal'_apply_ne _ _ _ h', Matrix.blockDiagonal'_apply_ne A _ _ h]

theorem sym_entry {n' : ℕ} (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n') (P Q : PairIx H Dw) :
    symPair (R := K) e' P (e' ⟨Q.1.1, Q.2.1⟩) (e' ⟨(starRingEnd ℂ).comp Q.1.1, Q.2.2⟩) = if P = Q then 1 else 0 := by
  obtain ⟨⟨τ, hτ⟩, i, k⟩ := P
  obtain ⟨⟨σ, hσ⟩, i', k'⟩ := Q
  have h2 : ¬ (e' ⟨σ, i'⟩ = e' ⟨(starRingEnd ℂ).comp τ, k⟩ ∧
      e' ⟨(starRingEnd ℂ).comp σ, k'⟩ = e' ⟨τ, i⟩) := by
    rintro ⟨h, -⟩
    have h5 : σ = (starRingEnd ℂ).comp τ := congrArg Sigma.fst (e'.injective h)
    exact conj_off H τ hτ (h5 ▸ hσ)
  simp only [symPair, Matrix.of_apply, if_neg h2, add_zero, e'.apply_eq_iff_eq]
  by_cases h : τ = σ
  · subst h
    simp [Sigma.mk.inj_iff, eq_comm]
    intro h5
    exact (conj_off H τ hτ (by rw [← h5]; exact hτ)).elim
  · have h3 : ¬ (σ = τ) := Ne.symm h
    simp [h, h3]
    intro h5
    exact (conj_off H τ hτ (by rw [← h5]; exact hσ)).elim

theorem L_eq_submatrix (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) {n n' : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
    (ε ε' : Fin Dw.dim ≃ PairIx H Dw) (L : Matrix (Fin Dw.dim) (Fin Dw.dim) K)
    (hL : ∀ j, Matrix.transpose (flatFrame A e e') * symPair (R := K) e (ε j) * flatFrame A e e' =
      ∑ k, L k j • symPair (R := K) e' (ε' k)) :
    L = (kronBlocks A).submatrix ε' ε := by
  ext a j
  have h := congrFun (congrFun (hL j) (e' ⟨(ε' a).1.1, (ε' a).2.1⟩)) (e' ⟨(starRingEnd ℂ).comp (ε' a).1.1, (ε' a).2.2⟩)
  rw [lhs_entry, Matrix.sum_apply] at h
  simp only [Matrix.smul_apply, sym_entry, smul_eq_mul, mul_ite, mul_one, mul_zero, ε'.apply_eq_iff_eq] at h
  rw [Finset.sum_ite_eq' Finset.univ a] at h
  simpa using h.symm

theorem det_kronBlocks (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) :
    (kronBlocks A).det = ∏ τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0},
      ((A τ.1).det ^ Dw.mult ((starRingEnd ℂ).comp τ.1) * (A ((starRingEnd ℂ).comp τ.1)).det ^ Dw.mult τ.1) := by
  rw [kronBlocks, GlobalTheory.Div.BlockChangeDet.det_blockDiagonal'_eq_prod]
  simp [Matrix.det_kronecker, Matrix.det_transpose]

theorem prod_pairs (f : (E →+* ℂ) → K) :
    ∏ τ : E →+* ℂ, f τ ^ (if τ (H.rt : E) = H.rt0 then Dw.q else Dw.p) =
      ∏ τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0},
        (f τ.1 ^ Dw.mult ((starRingEnd ℂ).comp τ.1) * f ((starRingEnd ℂ).comp τ.1) ^ Dw.mult τ.1) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0), Finset.prod_mul_distrib]
  congr 1
  · refine Finset.prod_congr (by convert rfl) fun τ _ => ?_
    rw [if_pos τ.2, Datum.mult, if_neg (conj_off H τ.1 τ.2)]
  · symm
    refine Fintype.prod_equiv
      { toFun := fun τ => ⟨(starRingEnd ℂ).comp τ.1, conj_off H τ.1 τ.2⟩
        invFun := fun σ => ⟨(starRingEnd ℂ).comp σ.1, conj_on H σ.1 σ.2⟩
        left_inv := fun τ => Subtype.ext (conj_conj_emb τ.1)
        right_inv := fun σ => Subtype.ext (conj_conj_emb σ.1) } _ _ (fun τ => ?_)
    simp only [Equiv.coe_fn_mk]
    rw [if_neg (conj_off H τ.1 τ.2), Datum.mult, if_pos τ.2]

end GlobalTheory.LogKSDiv.DetChange

theorem GlobalTheory.LogKSDiv.det_frameChange_balanced :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (K : Type) [Field K] (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) (n n' : ℕ)
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
    (ε ε' : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw) (L : Matrix (Fin Dw.dim) (Fin Dw.dim) K),
    (∀ j, _root_.Matrix.transpose (GlobalTheory.LogKSDiv.flatFrame A e e') * GlobalTheory.LogKSDiv.symPair (R := K) e (ε j) * GlobalTheory.LogKSDiv.flatFrame A e e' =
      ∑ k, L k j • GlobalTheory.LogKSDiv.symPair (R := K) e' (ε' k)) →
    ∃ u : K, (u = 1 ∨ u = -1) ∧
      L.det = u * ∏ τ : E →+* ℂ, (A τ).det ^ (if τ (H.rt : E) = H.rt0 then Dw.q else Dw.p) := by
  intro E _ _ _ H Dw K _ A n n' e e' ε ε' L hL
  classical
  rw [GlobalTheory.LogKSDiv.DetChange.L_eq_submatrix A e e' ε ε' L hL]
  have hs : (GlobalTheory.LogKSDiv.DetChange.kronBlocks A).submatrix ε' ε =
      ((GlobalTheory.LogKSDiv.DetChange.kronBlocks A).submatrix ε ε).submatrix (ε'.trans ε.symm) id := by
    ext a b; simp
  refine ⟨((Equiv.Perm.sign (ε'.trans ε.symm) : ℤ) : K), ?_, ?_⟩
  · rcases Int.units_eq_one_or (Equiv.Perm.sign (ε'.trans ε.symm)) with h | h <;> simp [h]
  · rw [hs, Matrix.det_permute, Matrix.det_submatrix_equiv_self, GlobalTheory.LogKSDiv.DetChange.det_kronBlocks,
      GlobalTheory.LogKSDiv.DetChange.prod_pairs]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleSpaceSectionIntersectionNumberEqBaseStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleSpace_section_intersectionNumber_eq_base : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), ∀ (y : Fin Y.dim → CartierDiv W.Z) (e : Fin Y.dim → Y.Dv), (∀ i, IsPull W.p₁ (y i) (e i) ∨ IsPull W.p₂ (y i) (e i)) → letI := algebraΓOfHom (W.p₁ ≫ Y.str); interNumRed F (⟨closure {W.δ (genericPoint Y.X)}, isClosed_closure⟩ : Closeds W.Z) (fun i => toLB (y i)) = Y.inter e := by
  first | exact @GlobalTheory.FlagPush.interNumRed_section | exact GlobalTheory.FlagPush.interNumRed_section | (intros; apply GlobalTheory.FlagPush.interNumRed_section <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosCombinationSmoothConeSymmIntFormStatement
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pos_combination_smoothCone_symmIntForm : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ r : ℕ, r ≤ g → ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → toReal b ∈ psdCone (id : ℤ → ℤ) (Fin r → ℤ) → ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ)) (cf : Fin m → ℕ), IsCone id φ γ ∧ (∀ j, 0 < cf j) ∧ b = ∑ j, cf j • γ j := by
  first | exact @GlobalTheory.ConeInterior.exists_pos_comb_int | exact GlobalTheory.ConeInterior.exists_pos_comb_int | (intros; apply GlobalTheory.ConeInterior.exists_pos_comb_int <;> assumption)
end

