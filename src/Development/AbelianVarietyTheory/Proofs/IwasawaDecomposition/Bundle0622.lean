import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0083
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0213
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleIsoOfAmpleDeterminantFrames
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0862
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
import Formalism.SharpRestriction.GrowthBounds.BaseLevels.LvSite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0605
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0037

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialSupportHolds
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorRef

section Form

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_periodForm {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W]
    [IsAdicComplete (maximalIdeal W) W] {t : SAB H (Sp W)}
    (P : PELUnif (maximalIdeal W) t) {ϖ : W} (hϖ : Irreducible ϖ) :
    ∃ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] ∧ ∀ y, y ≠ 0 → 0 < be y y := by
  letI := H.starRing
  choose Q hQ using QForm.exists_QVal hϖ P.D
  have hQ' : QForm.IsQ P.D.toPre ϖ Q := hQ
  have hex : ∀ χ, ∃ r, PsiCoord P.D.toPre χ r := fun χ =>
    ((GlobalTheory.PsiCoordLocal.main W P.D inferInstance χ).1).imp fun _ h => h.1
  have h0 : ∀ a, 0 ≤ Q a := fun a => by
    by_cases ha : a = 0
    · rw [ha, QForm.Q_zero hϖ P.D hQ']
    · exact zero_le_one.trans (QForm.Q_pos hϖ P.D hQ' ha)
  let be : LinearMap.BilinForm ℤ P.D.toPre.X :=
    LinearMap.mk₂ ℤ (fun a b => QForm.bHom hϖ P.D hQ' a b)
      (fun a a' b => by simp only [map_add, AddMonoidHom.add_apply])
      (fun c a b => by simp only [map_zsmul, AddMonoidHom.smul_apply, smul_eq_mul, zsmul_eq_mul, Int.cast_id])
      (fun a b b' => by simp only [map_add])
      (fun c a b => by simp only [map_zsmul, smul_eq_mul, zsmul_eq_mul, Int.cast_id])
  have hbe : ∀ a b, be a b = QForm.bOf P.D.toPre Q a b := fun _ _ => rfl
  refine ⟨be, ⟨fun a b => ?_, fun x a b => ?_, fun a b => ?_⟩, fun y => ?_, fun y hy => ?_⟩
  · rw [hbe, hbe, QForm.bOf_comm]
  · rw [hbe, hbe]
    exact QForm.bOf_balance hϖ P.D GlobalTheory.allSixLaws.1 P.oD hQ' x a b
  · simp
  · obtain ⟨r, hr⟩ := hex y
    obtain ⟨u, hu⟩ := GlobalTheory.ValForm.hasVal_coord (hQ y) hr
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (h0 y)
    rw [hn, zpow_natCast, ← map_pow, ← map_mul] at hu
    have e : r = u * ϖ ^ n := (IsFractionRing.injective W (FractionRing W) hu).trans (_root_.mul_comm _ _)
    refine ⟨u, fun _ => n, fun i => ?_, ?_⟩
    · have : i = 0 := Subsingleton.elim _ _
      subst this
      show be y y = _
      rw [hbe, ← QForm.two_Q_eq hϖ P.D hQ', hn]
    · simpa [e] using hr
  · rw [hbe, ← QForm.two_Q_eq hϖ P.D hQ']
    have := QForm.Q_pos hϖ P.D hQ' hy
    omega

end Form

theorem mem_support_iff_of_idlAlong {X : Scheme.{0}} (J : X.IdealSheafData) {W : Type} [CommRing W] [IsDomain W]
    [IsLocalRing W] (χ : Sp W ⟶ X) {ϖ : W} (hϖ : Irreducible ϖ) {n : ℕ} (h : idlAlong J χ = Ideal.span {ϖ ^ n}) :
    χ (closedPoint W : Sp W) ∈ J.support ↔ n ≠ 0 := by
  refine (mem_support_iff_stalkId J _).trans (not_congr ?_)
  unfold idlAlong at h
  constructor
  · intro hne
    rw [hne, Ideal.map_top] at h
    have hu : IsUnit (ϖ ^ n) := Ideal.span_singleton_eq_top.1 h.symm
    by_contra hn
    exact hϖ.not_isUnit ((isUnit_pow_iff hn).1 hu)
  · rintro rfl
    by_contra hne
    rw [pow_zero, Ideal.span_singleton_one] at h
    have hle : (FinalTheorems.stalkId J (χ (closedPoint W : Sp W))).map (Scheme.stalkClosedPointTo χ).hom ≤ maximalIdeal W := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha hua
      have : IsUnit a := isUnit_of_map_unit (Scheme.stalkClosedPointTo χ).hom a hua
      exact hne (Ideal.eq_top_of_isUnit_mem _ ha this)
    rw [h] at hle
    exact (maximalIdeal.isMaximal W).ne_top (top_le_iff.1 hle)

section Trait

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_unif_ext (T : CDVR) (t : SAB H (Sp T.V)) (hp : PolAt t (jK T.V)) :
    ∃ (T' : CDVR) (φ : T.V →+* T'.V) (t' : SAB H (Sp T'.V)), Function.Injective φ ∧ IsLocalHom φ ∧
      Nonempty (SABMap t' t (spMap φ)) ∧ Nonempty (PELUnif (maximalIdeal T'.V) t') := by
  let F := AlgebraicClosure (FractionRing T.V)
  have hF : Function.Injective (algebraMap T.V F) := by
    rw [IsScalarTower.algebraMap_eq T.V (FractionRing T.V) F]
    exact (algebraMap (FractionRing T.V) F).injective.comp (IsFractionRing.injective T.V _)
  have : FaithfulSMul T.V F := (faithfulSMul_iff_algebraMap_injective _ _).2 hF
  have : Algebra.IsAlgebraic T.V F := (IsFractionRing.comap_isAlgebraic_iff (K := FractionRing T.V)).2 inferInstance
  obtain ⟨W, hd, hc, hf, hs⟩ := GlobalTheory.Ex.UnifModel.exists_split T.V F t.G t.semi
  have hi : Function.Injective (algebraMap T.V W) := fun _ _ h => hF (congrArg (fun z : W => (z : F)) h)
  have hz : CharZero W := charZero_of_injective_ringHom hi
  have : FaithfulSMul T.V W := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have hl : IsLocalHom (algebraMap T.V W) := inferInstance
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull CubePf.cubePull (spMap (algebraMap T.V W)) t
  have j : Function.Injective ((algebraMap W (FractionRing W)).comp (algebraMap T.V W)) :=
    (IsFractionRing.injective W _).comp hi
  let g : FractionRing T.V →+* FractionRing W := IsFractionRing.lift j
  have hp' := GlobalTheory.DatUniq.polAt_pull m hp (jK W) (spMap g)
    ((GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).symm)
  obtain ⟨P, -⟩ := GlobalTheory.LN.uDvrSt_holds E H W ⟨hd, hc, hz⟩ _ hp' hs
  exact ⟨{ V := W }, algebraMap T.V W, _, hi, hl, ⟨m⟩, ⟨P⟩⟩

theorem closed_mem_abLocus_iff (T : CDVR) {t : SAB H (Sp T.V)} (P : PELUnif (maximalIdeal T.V) t) :
    (closedPoint T.V : Sp T.V) ∈ abLocus t.G ↔ Subsingleton P.D.toPre.X := by
  constructor
  · intro hc
    have hmax : (maximalIdeal T.V ^ (0 + 1)).IsMaximal := by
      rw [zero_add, pow_one]; infer_instance
    have hF : IsField (T.V ⧸ maximalIdeal T.V ^ (0 + 1)) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
    have hle : maximalIdeal T.V ^ (0 + 1) ≤ (closedPoint T.V).asIdeal := by
      rw [zero_add, pow_one]; exact le_rfl
    obtain ⟨q, hq⟩ : closedPoint T.V ∈ Set.range (PrimeSpectrum.comap
        (Ideal.Quotient.mk (maximalIdeal T.V ^ (0 + 1)))) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
      exact hle
    let g := P.U.gt 0
    have m : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
    have hq' : thick T.V (maximalIdeal T.V) 0 q ∈ abLocus t.G := by
      rw [← hq] at hc; exact hc
    exact ArcNotAbelian.subsingleton_of_mem_abLocus t.G t.semi _ hF _ q hq' P.D.toPre.X g.i g.i_hom
  · intro hs K _ _ s _
    have := (isAbelianScheme_of_unif_of_subsingleton GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 T.V T.cpl P.D P.A t.G t.semi
      P.U hs).proper
    infer_instance

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem charZero_of_point {K : CommRingCat.{0}} [Nontrivial K] (y : Spec K ⟶ Xo.XF c) : CharZero K := by
  let f := Spec.preimage (y ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
  exact charZero_of_injective_ringHom f.hom.injective

open GlobalTheory.HomExt in

theorem exists_base_trait (Z : Model Xo c β) (hβ : IsDedFrac β) (x : Z.X) :
    ∃ (T : CDVR) (χ : Sp T.V ⟶ Z.X) (y : Sp (FractionRing T.V) ⟶ Xo.XF c),
      χ (closedPoint T.V : Sp T.V) = x ∧ y ≫ Z.j = jK T.V ≫ χ := by
  by_cases hx : x ∈ Set.range Z.j
  · obtain ⟨u, rfl⟩ := hx
    let K := (Xo.XF c).residueField u
    have : CharZero K := charZero_of_point ((Xo.XF c).fromSpecResidueField u)
    obtain ⟨h₁, h₂, h₃⟩ := (GlobalTheory.FrameCmp.cDvr_powerSeries K : CDvr (PowerSeries K))
    let a : Sp (PowerSeries K) ⟶ Xo.XF c := spMap (PowerSeries.C (R := K)) ≫ (Xo.XF c).fromSpecResidueField u
    refine ⟨{ V := PowerSeries K }, a ≫ Z.j, jK _ ≫ a, ?_, Category.assoc _ _ _⟩
    exact (Scheme.Hom.comp_apply a Z.j _).trans (congrArg Z.j ((Scheme.Hom.comp_apply _ _ _).trans
      (Scheme.fromSpecResidueField_apply u _)))
  · obtain ⟨h₁, -, -, _, _, _, _⟩ := GlobalTheory.ModelRelCompare.densePart Z hβ
    obtain ⟨ξ, hξ, hs⟩ := exists_mem_genericPoints_specializes x
    have hξ' := genericPoints_subset_range_of_isDominant Z.j hξ
    have hne : ξ ≠ x := fun e => hx (e ▸ hξ')
    obtain ⟨W, _, _, _, a, h₀, h₁⟩ := exists_complete_discreteValuationRing_of_specializes hs hne
    obtain ⟨y, hy⟩ := exists_lift_of_range_subset Z.j
      (spMap (algebraMap W (FractionRing W)) ≫ a) (by
        rintro _ ⟨t, rfl⟩
        have : spMap (algebraMap W (FractionRing W)) t = (⊥ : PrimeSpectrum W) := by
          apply PrimeSpectrum.ext
          change Ideal.comap (algebraMap W (FractionRing W)) t.asIdeal = ⊥
          rw [@Ideal.eq_bot_of_prime _ _ t.asIdeal t.isPrime]
          exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)
        rw [Scheme.Hom.comp_apply, this]
        exact h₀ ▸ hξ')
    have hc : CharZero (FractionRing W) := charZero_of_point (K := .of (FractionRing W)) y
    have hc' : CharZero W := ⟨fun p q e => Nat.cast_injective (R := FractionRing W) (by
      simpa using congrArg (algebraMap W (FractionRing W)) e)⟩
    exact ⟨{ V := W }, a, y, h₁, hy⟩

theorem exists_trait (Z : Model Xo c β) (hβ : IsDedFrac β) (x : Z.X) :
    ∃ (T : CDVR) (χ : Sp T.V ⟶ Z.X) (t : SAB H (Sp T.V)) (_ : SABMap t Z.t χ) (_ : PELUnif (maximalIdeal T.V) t),
      χ (closedPoint T.V : Sp T.V) = x ∧ Set.range (jK T.V ≫ χ) ⊆ Set.range Z.j := by
  obtain ⟨T, χ, y, hx, hy⟩ := exists_base_trait Z hβ x
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull CubePf.cubePull χ Z.t
  have hp := GlobalTheory.GoodTrait.polAt_of_point Z m (jK T.V) y hy
  obtain ⟨T', φ, t', hi, hl, ⟨m'⟩, ⟨P⟩⟩ := exists_unif_ext T _ hp
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m'
  have j : Function.Injective ((algebraMap T'.V (FractionRing T'.V)).comp φ) :=
    (IsFractionRing.injective T'.V _).comp hi
  let g : FractionRing T.V →+* FractionRing T'.V := IsFractionRing.lift j
  have e : jK T'.V ≫ spMap φ = spMap g ≫ jK T.V :=
    (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).symm
  refine ⟨T', spMap φ ≫ χ, t', n, P, ?_, ?_⟩
  · exact (Scheme.Hom.comp_apply (spMap φ) χ _).trans ((congrArg χ (comap_closedPoint φ)).trans hx)
  · rintro _ ⟨p, rfl⟩
    refine ⟨(spMap g ≫ y) p, ?_⟩
    rw [← Scheme.Hom.comp_apply, Category.assoc, hy, ← Category.assoc, ← e, Category.assoc]

end Trait

theorem polSuppSt : PolSuppSt := by
  intro E _ _ _ H D l Xo c O _ β Z BD φ hβ hpos hdiv x
  obtain ⟨T, χ, t, m, P, rfl, hr⟩ := exists_trait Z hβ x
  have hW : CDvr T.V := ⟨T.dvr, T.cpl, T.ch0⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  obtain ⟨be, hbe, hmon, hpd⟩ := exists_periodForm P hϖ
  obtain ⟨n, hn, hid⟩ := hdiv T.V hW ϖ hϖ χ t m P hr be hbe hmon
  refine (mem_support_iff_of_idlAlong BD.idealSheaf χ hϖ hid).trans ?_
  refine Iff.trans ?_ (not_congr (abLocus_pullback abLocusOne Z.t.semi m.cart.1 _)).symm
  refine Iff.trans ?_ (not_congr (closed_mem_abLocus_iff T P)).symm
  constructor
  · intro hn0 hs
    apply hn0
    have h0 : φ.evalZ be = 0 := φ.eval_of_subsingleton _
    rw [h0] at hn
    exact_mod_cast hn
  · intro hs hn0
    have hnt : Nontrivial P.D.toPre.X := not_subsingleton_iff_nontrivial.1 hs
    have := hpos P.D.toPre.X be hbe hpd
    rw [← hn, hn0] at this
    simp at this

end GlobalTheory.TorRef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartGluing
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.PlkPt

theorem plk_smul {S ι : Type} [CommRing S] {M k : ℕ} (γ : S) (c : ι → Fin (M + 1) → S) (e : Fin k → ι) :
    plk (fun z => γ • c z) e = γ ^ k • plk c e := by
  funext q
  have h := Matrix.det_smul (Matrix.of fun l l' => c (e l) (plE M k q l')) γ
  rw [Fintype.card_fin] at h
  exact h

theorem valF_unit_ne {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)ˣ) : valF x U f.val ≠ 0 := by
  rw [valF, dif_pos h]
  exact ((f.isUnit.map _).map _).ne_zero

theorem top_le_pre {A : Type} [CommRing A] {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (φ : Γ(X, U) →+* A) :
    ⊤ ≤ (spMap φ ≫ hU.fromSpec) ⁻¹ᵁ U := by
  have h := (spMap φ).preimage_mono hU.fromSpec_preimage_self.ge
  exact h

theorem spMap_dualMap_id' (R : Type) [CommRing R] : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
  have : dualMap (RingHom.id R) = RingHom.id _ := by
    refine RingHom.ext fun x => ?_
    ext <;> simp [dualMap]
  rw [this]
  exact Spec.map_id _

theorem plk_pt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Pre Y i₀) (L : FinLB (Y Z.i).X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd (Y Z.i).t L M) (ι : Fin Z.m → Fin L.n) (ρ : ∀ a, Γ((Y Z.i).X, L.U (ι a)) →+* Γ(Z.X, (Z.U a).1)) (g : ∀ en : En Dw.mult, Z.X ⟶ PSpace (Z.i.c.V W) (plN M en.1)), Comparison₂ Z L aff crd ι ρ g → ∀ (k : Type) [Field k] a i (φ : Γ(Z.X, (Z.U a).1) →+* k) (ψ : Γ((Y Z.i).X, L.U i) →+* k), spMap ψ ≫ (aff i).fromSpec = spMap φ ≫ Z.chart a ≫ Z.π → ∀ en : En Dw.mult, ∃ hu, spMap φ ≫ Z.chart a ≫ g en = pt (φ.comp ((Z.alg a).comp (Z.i.c.V W).subtype)) (plk (fun z : Let Dw.mult => crd i k ψ ((Z.fr a).bc φ z.1 z.2)) en.2.1) hu := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z L aff M crd ι ρ g T k _ a i φ ψ hψ en
  obtain ⟨hu, h⟩ := T.plk a en
  have hφ : spMap (φ.comp (ρ a)) ≫ (aff (ι a)).fromSpec = spMap φ ≫ Z.chart a ≫ Z.π := by
    rw [← T.res a, ← Category.assoc]
    congr 1
    exact Spec.map_comp _ _
  have tan : ∀ z : Let Dw.mult, IsTanAtG (Y Z.i).t (spMap (ρ a) ≫ (aff (ι a)).fromSpec) (Z.fr a z.1 z.2) := by
    intro z
    have h1 := ((T.frame a _ (RingHom.id _)).1 z.1 z.2).1
    have h2 : spMap (RingHom.id Γ(Z.X, (Z.U a).1)) = 𝟙 _ := Spec.map_id _
    rw [h2, Category.id_comp, Vecs.bc, spMap_dualMap_id', Category.id_comp] at h1
    rw [T.res a]
    exact h1
  have nat : (fun z : Let Dw.mult => φ ∘ crd (ι a) _ (ρ a) (Z.fr a z.1 z.2)) =
      fun z : Let Dw.mult => crd (ι a) k (φ.comp (ρ a)) ((Z.fr a).bc φ z.1 z.2) :=
    funext fun z => (T.emb.nat (ι a) _ k (ρ a) φ _ (tan z)).symm
  have hγ : valF (spMap ψ ≫ (aff i).fromSpec) _ (L.g i (ι a)).val ≠ 0 := by
    refine valF_unit_ne _ _ ?_ _
    have h1 := top_le_pre (aff i) ψ
    have h2 := top_le_pre (aff (ι a)) (φ.comp (ρ a))
    rw [hφ, ← hψ] at h2
    exact le_inf h1 h2
  have tr : (fun z : Let Dw.mult => crd i k ψ ((Z.fr a).bc φ z.1 z.2)) =
      fun z : Let Dw.mult => valF (spMap ψ ≫ (aff i).fromSpec) _ (L.g i (ι a)).val •
        crd (ι a) k (φ.comp (ρ a)) ((Z.fr a).bc φ z.1 z.2) :=
    funext fun z => T.emb.trans i (ι a) k ψ (φ.comp (ρ a)) _ (hψ.trans hφ.symm)
      (by rw [hψ]; exact ((T.frame a k φ).1 z.1 z.2).1)
  have key : plk (fun z : Let Dw.mult => crd i k ψ ((Z.fr a).bc φ z.1 z.2)) en.2.1 =
      (Units.mk0 _ hγ) ^ en.1 • (φ ∘ plk (fun z : Let Dw.mult => crd (ι a) _ (ρ a) (Z.fr a z.1 z.2)) en.2.1) := by
    rw [map_plk, nat, tr, plk_smul]
    rfl
  have hv := span_range_comp_eq_top _ hu φ
  refine ⟨key ▸ span_range_units_smul hv _, ?_⟩
  rw [h, GlobalTheory.ProjSpace.spMap_pt]
  exact (pt_eq_pt_iff _ _ _).2 ⟨_, key⟩

end GlobalTheory.FlagEmb.PlkPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageOpensEqRangeOfValuative
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
namespace GlobalTheory

theorem preimage_opens_eq_range_of_valuative (F Z X : Scheme.{0}) (j : F ⟶ Z) (π : Z ⟶ X) (U : X.Opens)
    (hj : IsOpenImmersion j) (hd : Dense (Set.range j)) (hπ : IsSeparated π)
    (hF : TopologicalSpace.NoetherianSpace F) (hU : Set.range (j ≫ π) ⊆ (U : Set X))
    (hv : ∀ (A K : Type) [CommRing A] [IsDomain A] [ValuationRing A] [Field K] [Algebra A K]
      [IsFractionRing A K] (a : Sp K ⟶ F) (b : Sp A ⟶ X), Set.range b ⊆ (U : Set X) →
      a ≫ j ≫ π = spMap (algebraMap A K) ≫ b →
      ∃ l : Sp A ⟶ F, spMap (algebraMap A K) ≫ l = a ∧ l ≫ j ≫ π = b) :
    π ⁻¹' (U : Set X) = Set.range j := by
  have hg : Set.range (j ≫ π).base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]; exact hU
  let g : F ⟶ U := IsOpenImmersion.lift U.ι (j ≫ π) hg
  have hgfac : g ≫ U.ι = j ≫ π := IsOpenImmersion.lift_fac _ _ _
  have hj' : Set.range j.base ⊆ Set.range (π ⁻¹ᵁ U).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hU ⟨x, rfl⟩
  let j' : F ⟶ (π ⁻¹ᵁ U : Z.Opens) := IsOpenImmersion.lift (π ⁻¹ᵁ U).ι j hj'
  have hj'fac : j' ≫ (π ⁻¹ᵁ U).ι = j := IsOpenImmersion.lift_fac _ _ _
  have hcomp : j' ≫ (π ∣_ U) = g := by
    rw [← cancel_mono U.ι, hgfac, Category.assoc, morphismRestrict_ι, ← Category.assoc, hj'fac]
  haveI : QuasiCompact g := ⟨fun V _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  haveI : UniversallyClosed g := by
    apply UniversallyClosed.of_valuativeCriterion
    intro S
    obtain ⟨l, hl1, hl2⟩ := hv S.R S.K S.i₁ (S.i₂ ≫ U.ι)
      (by
        rintro _ ⟨x, rfl⟩
        rw [← Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
        exact ⟨_, rfl⟩)
      (by rw [← hgfac, ← Category.assoc, S.commSq.w, Category.assoc])
    have hl3 : l ≫ g = S.i₂ := by
      rw [← cancel_mono U.ι, Category.assoc, hgfac, hl2]
    exact ⟨⟨{ l := l, fac_left := hl1, fac_right := hl3 }⟩⟩
  haveI : UniversallyClosed (j' ≫ (π ∣_ U)) := by rw [hcomp]; infer_instance
  haveI : IsSeparated ((π ⁻¹ᵁ U).ι ≫ π) := inferInstance
  haveI : IsSeparated ((π ∣_ U) ≫ U.ι) := by rw [morphismRestrict_ι]; infer_instance
  haveI : IsSeparated (π ∣_ U) := IsSeparated.of_comp (π ∣_ U) U.ι
  haveI : UniversallyClosed j' := UniversallyClosed.of_comp_of_isSeparated j' (π ∣_ U)
  have hclosed : IsClosed (Set.range j'.base) := j'.isClosedMap.isClosed_range
  have hrange : Set.range j' = (π ⁻¹ᵁ U).ι ⁻¹' Set.range j := by
    ext w; constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, by rw [← hj'fac, Scheme.Hom.comp_apply]⟩
    · rintro ⟨x, hx⟩
      refine ⟨x, (π ⁻¹ᵁ U).ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hj'fac, hx]
  have hdense : Dense (Set.range j') := by
    rw [hrange]; exact hd.preimage (π ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap
  have huniv : Set.range j' = Set.univ := by
    rw [← hclosed.closure_eq]; exact hdense.closure_eq
  ext z; constructor
  · intro hz
    have hz' : z ∈ Set.range (π ⁻¹ᵁ U).ι := by rw [Scheme.Opens.range_ι]; exact hz
    obtain ⟨w, rfl⟩ := hz'
    obtain ⟨x, rfl⟩ : w ∈ Set.range j' := huniv ▸ Set.mem_univ w
    exact ⟨x, by rw [← hj'fac, Scheme.Hom.comp_apply]⟩
  · rintro ⟨x, rfl⟩; exact hU ⟨x, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PushExLeft
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) {g : ℕ}
  {ty : Fin g → (E →+* ℂ)} {σ₀ : KA l →+* ℂ} (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n)
  (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X)

def liftEx (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    (z : Fin g → ℂ) : Sp ℂ ⟶ Z.oF.t.G.left :=
  Z.m0.toSABMap.cart.1.lift (Fu.ex i P z).left y (by rw [Over.w (Fu.ex i P z), ← hu]; rfl)

def pushEx (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p) (z : Fin g → ℂ) : Over.mk p ⟶ Z.t.G :=
  Over.homMk (liftEx Z Fu y i P hu z ≫ Z.m.φ) (by
    show (liftEx Z Fu y i P hu z ≫ Z.m.φ) ≫ Z.t.G.hom = p
    rw [Category.assoc, Z.m.cart.1.w, ← Category.assoc, liftEx, IsPullback.lift_snd, ← hp])

theorem liftEx_fst (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    (z : Fin g → ℂ) : liftEx Z Fu y i P hu z ≫ Z.m0.toSABMap.φ = (Fu.ex i P z).left :=
  IsPullback.lift_fst _ _ _ _

theorem liftEx_snd (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    (z : Fin g → ℂ) : liftEx Z Fu y i P hu z ≫ Z.oF.t.G.hom = y :=
  IsPullback.lift_snd _ _ _ _

theorem pushEx_left (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p) (z : Fin g → ℂ) :
    (pushEx Z Fu y i P p hu hp z).left = liftEx Z Fu y i P hu z ≫ Z.m.φ := rfl

end GlobalTheory.ShFam.Hor.LogCh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlacesAvoidAuxiliaryStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_places_avoid_auxiliary : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (Q : Finset (PlE D.host))
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (sp : PlE D.host → SplitPlace D.host.E),
    (∀ v, NG.OverPl (Pq v) v) → (∀ P ∈ Q, IsSplitPl D.host P) →
    (∀ P ∈ Q, P ∉ T.pD i ∧ ∀ k' : Fin 2, P ∉ placesOver D.host.E (D.host.g k')) → (∀ P ∈ T.pD i, IsSplitPl D.host P) →
    (∀ P, (P ∈ qpOf D Pq Q ∨ P ∈ qpOf D Pq (T.pD i) ∨ ∃ kv, P = NX.pG D kv) → (sp P).w = P) →
    (∀ P P', (P ∈ qpOf D Pq Q ∨ P ∈ qpOf D Pq (T.pD i) ∨ ∃ kv, P = NX.pG D kv) →
      (P' ∈ qpOf D Pq Q ∨ P' ∈ qpOf D Pq (T.pD i) ∨ ∃ kv, P' = NX.pG D kv) → (sp P).v = (sp P').v → P = P') ∧
    (∀ P ∈ qpOf D Pq Q, P ∉ qpOf D Pq (T.pD i)) ∧ (∀ kv, NX.pG D kv ∉ qpOf D Pq Q ∧ NX.pG D kv ∉ qpOf D Pq (T.pD i)) ∧
    ∀ kv kv', NX.pG D kv = NX.pG D kv' → kv = kv' := by
  first | exact @GlobalTheory.LevelPlaceSep.levelPlaces_sep | exact GlobalTheory.LevelPlaceSep.levelPlaces_sep | (intros; apply GlobalTheory.LevelPlaceSep.levelPlaces_sep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepTiesD
section
noncomputable section

namespace GlobalTheory.Mem.Top.KerOne.CertEq

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.ChartsLv Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
  (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}

set_option maxHeartbeats 4000000 in

def StepTiesD {i : ℕ} (hi : i + 1 ≤ D.R.m) (Fo : FormsIn M (i + 1) hi) (S : StepD X0 u w hg Fo) (c : LatCmp D) : Prop :=
  (∀ (β : Fo.Ch) (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal)
    (x : GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] w'.adicCompletion D.host.F)),
    x ∈ UPts D.sp.cm.sig (D.sp.X (i + 1)).gram (w'.adicCompletion D.host.F) →
    (∀ a b, (((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x * frB X0 u w hg S.B w' h : GL (Fin (D.sp.X (i + 1)).rank) _) :
        Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈ w'.adicCompletionIntegers D.host.F) →
    (∀ a b, ((((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x * frB X0 u w hg S.B w' h)⁻¹ : GL (Fin (D.sp.X (i + 1)).rank) _) :
        Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈ w'.adicCompletionIntegers D.host.F) →
    x ∈ ulocOf Fo β w') ∧
  (∀ (β : Fo.Ch) (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal)
    (x : GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] w'.adicCompletion D.host.F)), x ∈ ulocOf Fo β w' →
    (∀ a b, (((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x * frB X0 u w hg S.B w' h : GL (Fin (D.sp.X (i + 1)).rank) _) :
        Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈ w'.adicCompletionIntegers D.host.F) ∧
    (∀ a b, ((((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x * frB X0 u w hg S.B w' h)⁻¹ : GL (Fin (D.sp.X (i + 1)).rank) _) :
        Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈ w'.adicCompletionIntegers D.host.F)) ∧
  (∀ w' ∈ Fo.bad, ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal) ∧
  cT (sigD D : D.host.E →+* D.host.E) (reGL (rankN D (i + 1) hi) D.host.E S.B).1 * gramN D (i + 1) hi *
    (reGL (rankN D (i + 1) hi) D.host.E S.B).1 = 1 ∧
  (∀ β, UnitCharacterChartCompatibility hi (Fo.K β).lev (c.embW u w hg) (S.ψ β)) ∧
  (∀ β cl, ∃ r : D.what₂.LL, D.what₂.embLL r = ((Fo.tw β).ch ((Fo.K β).y cl) : ℂ)) ∧
  Fo.okW w ∧
  ¬ D.what₂.places.resChar w ∣ Fo.T

end GlobalTheory.Mem.Top.KerOne.CertEq

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvLinearCombinationStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tanEv_linear_combination : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (k : Type) [CommRing k] (x : Sp k ⟶ X) (V : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V), ∀ (m : ℕ) (v : Fin m → (Sp (DualNumber k) ⟶ t.G.left)) (hv : ∀ i, IsTanAtG t x (v i)) (cf : Fin m → k) (w : Sp (DualNumber k) ⟶ t.G.left) (hw : IsTanAtG t x w), IsCombAtG t x v cf w → ∀ s : Γ(GlobalTheory.LieVB.omega t.G, V), tanEv t hw h s = ∑ i, cf i * tanEv t (hv i) h s := by
  first | exact @GlobalTheory.LocM.tanEv_comb | exact GlobalTheory.LocM.tanEv_comb | (intros; apply GlobalTheory.LocM.tanEv_comb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentFamilyOfUniqueLiftPrimeStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_family_of_unique_lift_prime : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (p : ℕ) (C : Formalism.MainNotions.DIV.Cons.SCF p) (b : Bool) (xO : Sp ↥(intO ↥C.S) ⟶ X), p.Prime → (∀ y : Sp ↥(intO ↥C.S) ⟶ X, spMap (intO ↥C.S).subtype ≫ y = spMap (intO ↥C.S).subtype ≫ xO → y = xO) → ∀ (m : ℕ) (u : Fin m → (Sp (DualNumber ↥C.S) ⟶ t.G.left)), (∀ i, IsTanAtG t (spMap (intO ↥C.S).subtype ≫ xO) (u i)) → (∀ cf cf' w, IsCombAtG t (spMap (intO ↥C.S).subtype ≫ xO) u cf w → IsCombAtG t (spMap (intO ↥C.S).subtype ≫ xO) u cf' w → cf = cf') → ∀ i, 0 < GlobalTheory.ShFam.Pad.grNorm t (spMap (intO ↥C.S).subtype ≫ xO) (lat t p (spMap (intO ↥C.S).subtype ≫ xO) b) u i := by
  first | exact @GlobalTheory.GrNormPos.grNorm_pos | exact GlobalTheory.GrNormPos.grNorm_pos | (intros; apply GlobalTheory.GrNormPos.grNorm_pos <;> assumption)
end

