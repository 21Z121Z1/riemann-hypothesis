import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3439
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3452
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcInTraceArc
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.SqrtNegDiscMemCoeffField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0609
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalPair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0467
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3455
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2790
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSysUOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalModelCartierDivisorThetaSetup
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3334
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3448
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3457
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3443

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelIsometryExtensionAlgClosed
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat

theorem exists_xfLevel_ext {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : GlobalTheory.Mum.Base R)
    (C : GlobalTheory.UChart.Fam Xo c R) (tK : SAB H (Sp (FractionRing R)))
    (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _))
    (I₀ : letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD (AlgebraicClosure (FractionRing R)))
    (hI₀ : GlobalTheory.LowDat.XFLevel C tK m1 m2 (AlgebraicClosure (FractionRing R)) I₀)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] :
    ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F), GlobalTheory.LowDat.XFLevel C tK m1 m2 F I ∧
      ∀ n a, (I.ev n a).y = (I₀.ev n a).y := by
  have hLL := GlobalTheory.firstFiveLaws
  have hL : Laws := hLL.1
  have hL₂ : Laws2 := hLL.2.1
  haveI : CharZero R := hR.2
  haveI : IsNoetherianRing R := hR.1.1
  haveI : CharZero (FractionRing R) := charZero_of_injective_ringHom (IsFractionRing.injective R (FractionRing R))
  haveI : CharZero (AlgebraicClosure (FractionRing R)) :=
    charZero_of_injective_ringHom (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))).injective
  have hB := C.P.D.tau_bimult
  have he := C.P.D.psi_even
  let s : AlgebraicClosure (FractionRing R) →ₐ[FractionRing R] F := IsAlgClosed.lift
  have hs : s.toRingHom.comp (algebraMap (FractionRing R) _) = algebraMap (FractionRing R) F := s.comp_algebraMap
  have hj : spMap s.toRingHom ≫ jFK (R := R) (AlgebraicClosure (FractionRing R)) = jFK (R := R) F := by
    rw [jFK, jFK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hs]
  let I := GlobalTheory.ArcExt.tateExt s.toRingHom hs hB hL I₀ (GlobalTheory.ArcOfModel.weilQkIs_qkExt hL hL₂ he hB s.toRingHom hs)
  have hext : ∀ n a, QkExt s.toRingHom (I₀.ev n a) (I.ev n a) := fun n a =>
    (GlobalTheory.TorusExt.qkExt_iff hB _ hs _ _).2 rfl
  refine ⟨I, ⟨?_, ?_⟩, fun n a => (hext n a).1⟩
  · show ((Units.map s.toRingHom.toMonoidHom (I₀.ζ l.M') : Fˣ) : F) = _
    rw [Units.coe_map]
    show s.toRingHom ((I₀.ζ l.M' : AlgebraicClosure (FractionRing R))) = _
    rw [hI₀.1]
    simp only [toF, RingHom.comp_apply]
    exact s.commutes _
  · intro k a σ hk x hx
    have hk1 : 1 ≤ k := by
      rcases hk with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact l.A_pos
      · have := l.three_le; omega
    have hT := GlobalTheory.FlatTors.torsionIso_holds E H R (maximalIdeal R) hR.1 C.t C.P
    obtain ⟨f₀, f₀₁, -⟩ := hT (AlgebraicClosure (FractionRing R)) k hk1
    obtain ⟨fF, fF₁, -⟩ := hT F k hk1
    obtain ⟨g₀, hg₁, hg₂⟩ := hI₀.2 k a σ hk (f₀ (I₀.ev k a)) ((f₀₁ _ _).2 rfl)
    let x' : TFK (R := R) F ⟶ C.P.A.A :=
      (Over.homMk (spMap s.toRingHom) hj : TFK (R := R) F ⟶ TFK (R := R) (AlgebraicClosure (FractionRing R))) ≫
        f₀ (I₀.ev k a)
    have hx' : C.P.ToA F k (I.ev k a) x' :=
      (GlobalTheory.TorsionExt.qkToAkU_iff_of_qkExt hLL R (maximalIdeal R) hR.1 C.P.D C.P.A C.t.G C.t.semi C.P.U _ F s k hk1
        (I₀.ev k a) (I.ev k a) _ x' (hext k a) rfl).1 ((f₀₁ _ _).2 rfl)
    have hxx : x = x' := ((fF₁ _ _).1 hx).trans ((fF₁ _ _).1 hx').symm
    refine ⟨spMap s.toRingHom ≫ g₀, ?_, ?_⟩
    · rw [Category.assoc, hg₁, hxx]
      simp only [x', Over.comp_left, Over.homMk_left, Category.assoc]
    · rw [Category.assoc, hg₂, ← hj]
      simp only [Category.assoc]

end GlobalTheory.LowDat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelIsometryGenericFibreBoundaryChart
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_tateIso_roots {Dw : Datum H} (l : Level H) {k : Type} [Field k] {Q : Type} [Group Q]
    {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso Dw k Q act e) (z : ℕ → kˣ)
    (hz : ∀ n, 0 < n → IsPrimitiveRoot (z n) n) (hzp : ∀ n m, 0 < n → 0 < m → z (n * m) ^ m = z n)
    (hA : z l.A = I.ζ l.A) :
    ∃ I' : TateIso Dw k Q act e, (∀ n, 0 < n → I'.ζ n = z n) ∧ (∀ a, I'.ev l.A a = I.ev l.A a) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), I'.ev l.M a = I.ev l.M a := by
  rcases Nat.eq_zero_or_pos (Dw.p + Dw.q) with h0 | hpq
  · have hs : Subsingleton Dw.La := AllClasses.subsingleton_of_rank_zero Dw h0
    have hEF : ∀ a b : Dw.La, Dw.EF a b = 0 := fun a b => by
      rw [Subsingleton.elim a 0, map_zero, LinearMap.zero_apply]
    refine ⟨{ I with ζ := z, ζ_prim := hz, ζ_pow := hzp, isom := fun n hn a b => ?_ }, fun _ _ => rfl,
      fun _ => rfl, fun _ _ => rfl⟩
    simpa [hEF] using I.isom n hn a b
  · exact GlobalTheory.LocM.RootsPrescribe.roots E H Dw l k Q act e I z hpq hz hzp hA

theorem exists_genFib {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)} (P : PELUnif I t)
    (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK t (jK R)) {S : Scheme.{0}} (t₀ : SAB H S)
    (z : Sp (FractionRing R) ⟶ S) (m2 : SABMap tK t₀ z) : letI := H.starRing;
    ∃ ψ₁ : P.A.A.left ⟶ tK.G.left, ψ₁ ≫ m1.φ = P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ∧
      IsGrpPullback P.A.A t₀.G z (ψ₁ ≫ m2.φ) ∧ LBIso P.A.L (t₀.PP.L.pull (ψ₁ ≫ m2.φ)) ∧
      ∀ a : 𝓞 E, (P.oA.act a).left ≫ ψ₁ ≫ m2.φ = (ψ₁ ≫ m2.φ) ≫ (t₀.act.act a).left := by
  letI := H.starRing
  have := P.U.gen_hom
  have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
  set k : P.A.A.left ⟶ t.G.left := P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) with hk
  have gpG : IsGrpPullback P.A.A t.G (jK R) k :=
    ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (jK R))).congr (Category.id_comp _) rfl
  let ψ₁ : P.A.A.left ⟶ tK.G.left := m1.cart.1.lift k P.A.A.hom gpG.1.w
  have hψ₁ : ψ₁ ≫ m1.φ = k := m1.cart.1.lift_fst _ _ _
  have hψ₂ : ψ₁ ≫ tK.G.hom = P.A.A.hom := m1.cart.1.lift_snd _ _ _
  have n : IsGrpPullback P.A.A t.G (𝟙 _ ≫ jK R) (ψ₁ ≫ m1.φ) :=
    gpG.congr (Category.id_comp _).symm hψ₁.symm
  have cart1 : IsGrpPullback P.A.A tK.G (𝟙 _) ψ₁ := m1.cart.cancel n (hψ₂.trans (Category.comp_id _).symm)
  have cart : IsGrpPullback P.A.A t₀.G z (ψ₁ ≫ m2.φ) := (cart1.comp m2.cart).congr (Category.id_comp _) rfl
  have actA : ∀ x, (P.oA.act x).left ≫ k = k ≫ (t.act.act x).left := by
    intro x
    have e : P.oA.act x ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (jK R)).map (t.act.act x) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (P.lin.ext x)).symm
    rw [hk, ← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  have actK : ∀ a : 𝓞 E, (P.oA.act a).left ≫ ψ₁ = ψ₁ ≫ (tK.act.act a).left := by
    intro a
    apply m1.cart.1.hom_ext
    · calc ((P.oA.act a).left ≫ ψ₁) ≫ m1.φ = (P.oA.act a).left ≫ k := by rw [Category.assoc, hψ₁]
        _ = k ≫ (t.act.act a).left := actA a
        _ = (ψ₁ ≫ (tK.act.act a).left) ≫ m1.φ := by rw [Category.assoc ψ₁, m1.act a, ← Category.assoc, hψ₁]
    · rw [Category.assoc, hψ₂, Over.w (P.oA.act a), Category.assoc, Over.w (tK.act.act a), hψ₂]

  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have B₁ : LBIso (P.A.L.pull (𝟙 _)) (P.U.LG.L.pull k) :=
    LBIso.chartPull (chartPullSame P.A.L (fun _ => 𝟙 _) (fun _ => P.U.gen.hom.left) _ P.U.gen.inv.left
        (fun _ => hgi.symm))
      (chartPullSame P.U.LG.L (fun _ => k) (fun _ => pullback.fst t.G.hom (jK R)) _ P.U.gen.inv.left
        (fun _ => rfl)) P.U.ext
  have B₁' : LBIso P.A.L (t.PP.L.pull k) := by
    rw [← P.bundle]
    exact LBIso.chartPull (chartPullUnpull P.A.L (𝟙 _) rfl) (chartPullId _) B₁
  obtain ⟨w₂, -, g₂, -⟩ := rigIso_congr rfl m1.cm m1.lin rfl rfl
  have B₂ : LBIso (tK.PP.L.pull ψ₁) (t.PP.L.pull k) :=
    LBIso.chartPull (chartPullPull tK.PP.L ψ₁)
      (chartPullSame t.PP.L (fun _ => k) (fun _ => m1.φ) _ ψ₁ (fun _ => hψ₁.symm)) ⟨w₂, g₂⟩
  obtain ⟨w₃, -, g₃, -⟩ := rigIso_congr rfl m2.cm m2.lin rfl rfl
  have B₃ : LBIso (tK.PP.L.pull ψ₁) (t₀.PP.L.pull (ψ₁ ≫ m2.φ)) :=
    LBIso.chartPull (chartPullPull tK.PP.L ψ₁)
      (chartPullSame t₀.PP.L (fun _ => ψ₁ ≫ m2.φ) (fun _ => m2.φ) _ ψ₁ (fun _ => rfl)) ⟨w₃, g₃⟩
  have BL : LBIso P.A.L (t₀.PP.L.pull (ψ₁ ≫ m2.φ)) :=
    LBIso.trans P.A.isLB (pull_isLB tK.PP.isLB _) (pull_isLB t₀.PP.isLB _)
      (LBIso.trans P.A.isLB (pull_isLB t.PP.isLB _) (pull_isLB tK.PP.isLB _) B₁' (LBIso.symm B₂)) B₃
  refine ⟨ψ₁, hψ₁, cart, BL, fun a => ?_⟩
  rw [← Category.assoc, actK, Category.assoc, m2.act a, Category.assoc]

end GlobalTheory.LowDat

namespace GlobalTheory.LowDat

theorem exists_xfLevel : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : GlobalTheory.UChart.Fam Xo c R) (tK : SAB H (Sp (FractionRing R)))
    (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _))
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
    ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F), GlobalTheory.LowDat.XFLevel C tK m1 m2 F I := by
  intro E _ _ _ H Dw l Xo c R _ _ _ hR C tK m1 m2 F _ _ _
  letI := H.starRing
  have := hR.2
  have hT := GlobalTheory.FlatTors.torsionIso_holds E H R _ hR.1 C.t C.P
  have hM' : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  let β : KA l →+* F := (toF C F).comp (IntermediateField.inclusion c.le).toRingHom
  have hx : (jFK (R := R) F ≫ C.y ≫ pullback.fst _ _) ≫ Xo.s = spMap β := by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc C.y, C.y_over]
    simp only [β, toF, spMap_comp, Category.assoc]
  obtain ⟨-, J0, hζ0, jA, jM⟩ := Xo.univ.geom F (jFK (R := R) F ≫ C.y ≫ pullback.fst _ _) β hx
  haveI := c.fin
  obtain ⟨w, hw1, hw2, hw3⟩ := GlobalTheory.HostModel.exists_roots c.F F (toF C F)
  have hwA : w l.A = J0.ζ l.A := Units.ext (by
    rw [hw3 l.A l.A_pos ⟨zeta l.A, c.le (IntermediateField.subset_adjoin _ _ (by simp))⟩ rfl, hζ0]
    rfl)
  obtain ⟨J, hJζ, hJA, hJM⟩ := exists_tateIso_roots l J0 w hw1 hw2 hwA
  obtain ⟨ψ₁, h1, gψ, lψ, aψ⟩ := exists_genFib C.P tK m1 Xo.univ.t (C.y ≫ pullback.fst _ _) m2
  obtain ⟨I, hI, eI⟩ := GlobalTheory.ArcOfPoint.exists_tateIsoQ Dw hR.1 C.P hT Xo.univ.t _ _ gψ lψ aψ F J
  refine ⟨I, ?_, ?_⟩
  · rw [hI, hJζ _ hM', hw3 _ hM' ⟨zeta l.M', c.zeta_mem⟩ rfl]
  · intro k a σ hσ x hx
    have hk : 0 < k := by
      rcases hσ with ⟨rfl, -⟩ | ⟨rfl, -⟩
      exacts [l.A_pos, by have := l.three_le; omega]
    have hJσ : toUnit _ ≫ σ = J.ev k a := by
      rcases hσ with ⟨rfl, rfl⟩ | ⟨rfl, ha, rfl⟩
      · rw [hJA]; exact jA a
      · rw [hJM a ha]; exact jM a ha
    obtain ⟨f, f₁, f₂, f₃, -⟩ := hT F k hk
    obtain ⟨e, he⟩ : ∃ e : (TFK (R := R) F ⟶ C.P.A.A) ≃*
        (Over.mk (jFK (R := R) F ≫ C.y ≫ pullback.fst _ _) ⟶ Xo.univ.t.G),
        ∀ x, (e x).left = x.left ≫ ψ₁ ≫ m2.φ := GlobalTheory.LiePull.exists_pushEquiv gψ (TFK (R := R) F) _ rfl
    have hx' : (e.symm (J.ev k a)).left ≫ ψ₁ ≫ m2.φ = (J.ev k a).left := by
      rw [← he, MulEquiv.apply_symm_apply]
    have hxk : e.symm (J.ev k a) ^ k = 1 := by
      rw [← map_pow, (J.onto k hk _).2 ⟨a, rfl⟩, map_one]
    obtain ⟨p, hp⟩ := f₂ _ hxk
    have hpe := eI k hk a p _ hx' ((f₁ p _).2 hp.symm)
    have hxx : x = e.symm (J.ev k a) := by
      rw [(f₁ _ _).1 hx, ← hp]; exact ((f₃ _ _).2 hpe).symm
    refine ⟨x.left ≫ ψ₁, by rw [Category.assoc, h1], ?_⟩
    rw [Category.assoc, hxx, hx', ← hJσ, Over.comp_left]
    have ht : (toUnit (Over.mk (jFK (R := R) F ≫ C.y ≫ pullback.fst _ _))).left =
        jFK (R := R) F ≫ C.y ≫ pullback.fst _ _ := by
      simpa using Over.w (toUnit (Over.mk (jFK (R := R) F ≫ C.y ≫ pullback.fst _ _)))
    rw [ht]
    simp only [Category.assoc]

end GlobalTheory.LowDat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleExtensionAtBoundaryPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BdStalkExt

theorem exists_extension_test {S X Y : Scheme.{0}} (g : X ⟶ S) [Smooth g] [QuasiCompact g] (e : Y ⟶ X)
    [IsOpenImmersion e] (x : S) [IsRegularLocalRing (S.presheaf.stalk x)] (L : LB Y) (hL : L.IsLB) :
    ∃ N : LB (pullback g (S.fromSpecStalk x)), N.IsLB ∧
      ∀ (T : Scheme.{0}) (a : T ⟶ pullback g (S.fromSpecStalk x)) (b : T ⟶ Y),
        a ≫ pullback.fst g (S.fromSpecStalk x) = b ≫ e → LBIso (N.pull a) (L.pull b) := by
  obtain ⟨N, hN, h⟩ := GlobalTheory.BdLocalExt.exists_extension_stalk g e x L hL
  refine ⟨N, hN, fun T a b hab => ?_⟩
  let t : T ⟶ pullback (e ≫ g) (S.fromSpecStalk x) :=
    pullback.lift b (a ≫ pullback.snd g (S.fromSpecStalk x)) (by
      rw [← Category.assoc, ← hab, Category.assoc, Category.assoc, pullback.condition])
  have ha : a = t ≫ pullback.map (e ≫ g) (S.fromSpecStalk x) g (S.fromSpecStalk x) e (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext
    · rw [hab, Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc]
    · rw [Category.assoc, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
  have hb : b = t ≫ pullback.fst (e ≫ g) (S.fromSpecStalk x) := (pullback.lift_fst _ _ _).symm
  exact LBIso.chartPull (chartPullSame N _ _ _ t fun _ => ha) (chartPullSame L _ _ _ t fun _ => hb) h

theorem exists_extension_at_boundary : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∀ x : S, x ∉ Set.range j → ∃ N : LB (pullback G.hom (S.fromSpecStalk x)), N.IsLB ∧ ∀ (T : Scheme.{0}) (a : T ⟶ pullback G.hom (S.fromSpecStalk x)) (b : T ⟶ tF.G.left), a ≫ pullback.fst G.hom (S.fromSpecStalk x) = b ≫ e → LBIso (N.pull a) (tF.PP.L.pull b) := by
  intro E _ _ _ H Dw l Xo c φ _ _ _ Z zs i OZ N d J S π j _ BD hU hpre tF _ G _ _ e hsa he _ x hx
  obtain ⟨-, -, -, -, ⟨-, hproj, -⟩, -⟩ := hU
  haveI := hsa.smooth
  haveI := hsa.quasiCompact
  haveI : LocallyOfFiniteType (π ≫ zs) := by
    obtain ⟨M, i', hi', hcomp⟩ := hproj
    haveI := hi'
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str c.F M
    rw [← hcomp]
    infer_instance
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  obtain ⟨k, _, m, n, C, ξ, a, -, -, rfl, het, -⟩ := hpre x hx
  haveI : IsRegularLocalRing (ChartRing k m n) :=
    GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin m ⊕ Fin n)
  haveI : IsRegularLocalRing (S.presheaf.stalk (ξ (closedPoint _))) :=
    (GlobalTheory.RegSmooth.isRegularLocalRing_of_isEtaleCompletion _ het).1
  haveI : IsOpenImmersion e := MorphismProperty.of_isPullback (P := @IsOpenImmersion) he.1.flip inferInstance
  exact exists_extension_test G.hom e _ tF.PP.L tF.PP.isLB

end GlobalTheory.BdStalkExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFormFactorThroughTraceGenerator
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem exists_int_eq_mul_of_ne_zero {E : Type} [Field E] [NumberField E] (t : 𝓞 E) (ht : t ≠ 0) :
    ∃ (N : ℤ) (c : 𝓞 E), N ≠ 0 ∧ (N : 𝓞 E) = t * c := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {t}))
  refine ⟨(Ideal.absNorm (Ideal.span {t}) : ℤ), c, ?_, ?_⟩
  · have : Ideal.absNorm (Ideal.span {t}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact ht
    exact_mod_cast this
  · rw [Int.cast_natCast, ← hc, mul_comm]

theorem eq_zero_of_forall_theta_mul {E : Type} [Field E] [NumberField E] {θ : 𝓞 E →+ ℤ} (hθ : θ ≠ 0)
    {t : 𝓞 E} (h : ∀ u, θ (t * u) = 0) : t = 0 := by
  by_contra ht
  obtain ⟨N, c, hN, hc⟩ := exists_int_eq_mul_of_ne_zero t ht
  apply hθ
  ext v
  have := h (c * v)
  rw [← mul_assoc, ← hc, ← zsmul_eq_mul, map_zsmul, smul_eq_mul] at this
  simpa [hN] using this

theorem exists_linear_theta_factor : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    (Z' : Submodule (𝓞 E) D.La) (θ : 𝓞 E →+ ℤ) (s : 𝓞 E) (hs : s ≠ 0)
    (hgen : ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u)) (w : D.La),
    ∃ ℓ : Z' →ₗ[𝓞 E] 𝓞 E, ∀ x : Z', θ (ℓ x) = D.EF x (H.bar s • w) := by
  intro E _ _ _ H D Z' θ s hs hgen w
  have hθ : θ ≠ 0 := by
    intro h0
    obtain ⟨i, hi⟩ : ∃ i, (Module.Free.chooseBasis ℤ (𝓞 E)).repr s i ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hs ((Module.Free.chooseBasis ℤ (𝓞 E)).repr.injective (by ext i; simp [hne i]))
    obtain ⟨t, ht⟩ := hgen ((Module.Free.chooseBasis ℤ (𝓞 E)).coord i).toAddMonoidHom
    have := ht 1
    simp [h0] at this
    exact hi this
  have uniq : ∀ t t' : 𝓞 E, (∀ u, θ (t * u) = θ (t' * u)) → t = t' := fun t t' h =>
    sub_eq_zero.1 (eq_zero_of_forall_theta_mul hθ fun u => by rw [sub_mul, map_sub, h, sub_self])
  let ψ : D.La → 𝓞 E →+ ℤ := fun x => AddMonoidHom.mk' (fun u => D.EF (u • x) w) (fun a b => by simp [add_smul])
  choose T hT using fun x : Z' => hgen (ψ x)
  refine ⟨{ toFun := T, map_add' := ?_, map_smul' := ?_ }, fun x => ?_⟩
  · intro x y
    apply uniq
    intro u
    rw [← hT (x + y) u, add_mul, map_add, ← hT x u, ← hT y u]
    simp [ψ, smul_add]
  · intro c x
    show T (c • x) = c * T x
    apply uniq
    intro u
    rw [← hT (c • x) u, show c * T x * u = T x * (c * u) by ring, ← hT x (c * u)]
    simp only [ψ, AddMonoidHom.mk'_apply, Submodule.coe_smul, smul_smul]
    rw [show s * u * c = s * (c * u) by ring]
  · show θ (T x) = _
    have := hT x 1
    rw [mul_one, mul_one] at this
    rw [← this]
    simp only [ψ, AddMonoidHom.mk'_apply]
    exact D.adj s x w

end GlobalTheory.LowFilt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemGenericPointsMemClosure
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc

theorem exists_mem_genericPoints_mem_closure (X : Scheme.{0}) (x : X) : ∃ η ∈ genericPoints X, x ∈ closure {η} := by
  obtain ⟨u, hu, hxu⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {x} isIrreducible_singleton
  have hc : IsClosed u := isClosed_of_mem_irreducibleComponents u hu
  have hi : IsIrreducible u := hu.prop
  have hg := hi.isGenericPoint_genericPoint_closure
  rw [hc.closure_eq] at hg
  refine ⟨hi.genericPoint, ?_, ?_⟩
  · show closure {hi.genericPoint} ∈ irreducibleComponents X
    rw [hg.def]; exact hu
  · rw [hg.def]; exact hxu rfl

theorem exists_uSetup_regular_at : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H),
    1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (x : Xo.XF c),
      ∃ (X' : USetup C) (w : X'.M.Z), X'.π w = C.i x ∧ X'.S.R ≤ X'.M.O w := by
  intro E _ _ _ H Dw hpq l Xo c C x
  obtain ⟨η, hη, hx⟩ := exists_mem_genericPoints_mem_closure (Xo.XF c) x
  obtain ⟨X, -, hX⟩ := GlobalTheory.UPoinc.GSetup.exists_uSetup E H Dw hpq l Xo c C η hη 0
  have hr : Set.range X.π = closure {C.i η} := GlobalTheory.UPoinc.USetup.range_π_eq E H Dw hpq l Xo c C X η _ hX rfl
  have hxr : C.i x ∈ Set.range X.π := by
    rw [hr, ← specializes_iff_mem_closure]
    exact (specializes_iff_mem_closure.2 hx).map C.i.continuous
  obtain ⟨w, hw⟩ := hxr
  obtain ⟨wi⟩ := nonempty_uWit X
  obtain ⟨U, c₀, hc, fg, frac, hth, hev, ρ', u', -, hwU, -, -, ⟨G, _, α, β, hα, hβ, hL, -⟩, hu'⟩ :=
    GlobalTheory.UPoinc.exists_urechart_affine E H Dw hpq l Xo c C X wi w ⟨x, hw.symm⟩
  let X' : USetup C :=
    { o₁ := X.o₁
      Ω₁ := X.Ω₁
      S := X.S.rechart c₀ hc (X.M.ringOn U) fg frac hth hev
      ρ := ρ'
      big := X.big
      u := u'
      pulled := ⟨G, _, α, β, hα, hβ, hL⟩
      gen := fun v => by rw [hu']; exact X.gen v
      M := X.M
      normal := X.normal
      π := X.π
      fin := X.fin
      comp := by
        rw [← Category.assoc, hu', X.comp]
        simp only [Category.assoc] }
  exact ⟨X', w, hw, RatModel.ringOn_le_O (M := X.M) hwU⟩

end GlobalTheory.UPoinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalModelCartierDivisorThetaSetupStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_model_cartierDivisor_thetaSetup : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W8 : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W8 → ThetaInt F W8 i → ∀ X₁ : Setup F W8 i, ∃ (ι : ℕ) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (D : GlobalTheory.EffCartierData Y.Z), 1 ≤ ι ∧ X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY ∧ IsProper πY ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y.Z ∧ (∀ y ∈ D.idealSheaf.support, X₁.π (πY y) ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a} := by
  first | exact @GlobalTheory.Poinc.exists_model_divisor_of_orders | exact GlobalTheory.Poinc.exists_model_divisor_of_orders | (intros; apply GlobalTheory.Poinc.exists_model_divisor_of_orders <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOneModMaximalMemOtherMaximalsOverNat
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

theorem GlobalTheory.sep_one_mod_maximal_mem_others : ∀ {E : Type} [Field E] [NumberField E] (n : ℕ) (hn : 0 < n) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal),
    ∃ e : 𝓞 E, e - 1 ∈ 𝔭 ∧ ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮 := by
  intro E _ _ n hn 𝔭 h𝔭
  have hn0 : (n : 𝓞 E) ≠ 0 := by exact_mod_cast hn.ne'
  have hI0 : Ideal.span {(n : 𝓞 E)} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  set S := (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(n : 𝓞 E)})).toFinset.erase 𝔭
    with hS
  have htop : 𝔭 ⊔ ∏ 𝔮 ∈ S, 𝔮 = ⊤ := by
    refine Ideal.sup_prod_eq_top fun 𝔮 h𝔮 => ?_
    rw [hS, Finset.mem_erase, Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hI0] at h𝔮
    obtain ⟨hne, hpr, hle⟩ := h𝔮
    have hbot : 𝔮 ≠ ⊥ := by
      rintro rfl
      rw [Ideal.span_le, Set.singleton_subset_iff] at hle
      exact hn0 hle
    have hmax : 𝔮.IsMaximal := hpr.isMaximal hbot
    by_contra hc
    have e1 : 𝔭 = 𝔭 ⊔ 𝔮 := h𝔭.eq_of_le hc le_sup_left
    have h2 : 𝔮 ≤ 𝔭 := e1 ▸ le_sup_right
    exact hne (hmax.eq_of_le h𝔭.ne_top h2)
  have h1 : (1 : 𝓞 E) ∈ 𝔭 ⊔ ∏ 𝔮 ∈ S, 𝔮 := htop ▸ Submodule.mem_top
  obtain ⟨p, hp, e, he, hpe⟩ := Submodule.mem_sup.mp h1
  refine ⟨e, ?_, fun 𝔮 hmax hn𝔮 hne => ?_⟩
  · have : e - 1 = -p := by rw [← hpe]; ring
    rw [this]; exact 𝔭.neg_mem hp
  · have hmem : 𝔮 ∈ S := by
      rw [hS, Finset.mem_erase, Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hI0]
      exact ⟨hne, hmax.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hn𝔮⟩
    exact Ideal.prod_le_inf.trans (Finset.inf_le hmem) he
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactificationGenericSubsetModuliStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_compactification_generic_subset_moduli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∃ W : C.Z.Opens, Set.range C.i ⊆ W ∧ ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z), Set.range (gPt p ≫ y) ⊆ W → Set.range (gPt p ≫ y) ⊆ Set.range C.i := by
  first | exact @GlobalTheory.UPoinc.exists_open_generic_subset_moduli | exact GlobalTheory.UPoinc.exists_open_generic_subset_moduli | (intros; apply GlobalTheory.UPoinc.exists_open_generic_subset_moduli <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalSiegelAdjointActionPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principal_siegel_adjoint_action_pullback : ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (bar : O → O) (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B) (f : S' ⟶ S) (z : SiegPre h M ζ s) (act : O → (z.A ⟶ z.A)), f ≫ s = s' → z.Principal → IsRAct z.A act → Adj z.A z.P bar act → ∃ (w : SiegPre h M ζ s') (actw : O → (w.A ⟶ w.A)), w.Principal ∧ IsRAct w.A actw ∧ Adj w.A w.P bar actw ∧ ActPB w actw z act f := by
  first | (exact @GlobalTheory.UPel.HT.siegPre_actPB_pullback) | (exact GlobalTheory.UPel.HT.siegPre_actPB_pullback) | (intros; apply GlobalTheory.UPel.HT.siegPre_actPB_pullback  <;> assumption)
end

